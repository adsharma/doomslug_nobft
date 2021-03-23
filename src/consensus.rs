use crate::types::{Balance, BlockHeight, Signature, ValidatorOrd};
use std::cmp::{max, min};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::time::{Duration, Instant};

const ENDORSEMENT_TIMEOUT: Duration = Duration::from_millis(100);
const INITIAL_SKIP_TIMEOUT: Duration = Duration::from_millis(1500);
const SKIP_TIMEOUT_STEP: Duration = Duration::from_millis(200);
const MAX_SKIP_TIMEOUT: Duration = Duration::from_millis(25000);

pub const MAX_HEIGHTS_TO_TRACK_AHEAD: BlockHeight = 1000;

/// Is responsible for determining when to issue an attestation.
/// The only external information it needs is the current head, and current time.
/// Once the head is updated, 100ms later issues an endorsement to the block
/// producer on the next height, and then with an increasing delay starting with
/// 1s sends non-endorsing attestations to each consecutive block producer.
/// Makes sure to not issue attestations that can potentially cause slashable
/// behavior.
pub struct AttestationIssuer {
    /// The `target_height` for the next attestation that will be issued
    target_height: BlockHeight,
    /// When was the timer last started (timer is restarted when the head is
    /// updated, as well as each time timer itself triggers).
    timer_started: Instant,

    /// The height of the current head of the chain. Determines the `source_height`
    /// for the attestations.
    head_height: BlockHeight,

    largest_attestation_height: BlockHeight,

    /// The last final block. Determines the delays in the timer.
    largest_final_height: BlockHeight,
}

/// For a particular pair of (`source_height`, `target_height`) tracks the total
/// stake of all the attestations with such source and target heights, and the
/// attestations themselves.
struct AttestationTrackerEntry {
    attested_stake: Balance,
    attestations: HashMap<ValidatorOrd, Signature>,
}

/// Tracks future attestations. Responsible for determining when a block can be
/// produced.
pub struct AttestationTracker {
    head_height: BlockHeight,

    attestations: HashMap<BlockHeight, HashMap<BlockHeight, AttestationTrackerEntry>>,
}

impl AttestationIssuer {
    pub fn new(now: Instant) -> Self {
        Self {
            target_height: 1,
            timer_started: now,

            head_height: 0,
            largest_attestation_height: 0,
            largest_final_height: 0,
        }
    }

    /// Computes for how long to sleep before issuing the next attestations.
    /// For endorsements the delay is always 100ms.
    /// For non-endorsing attestations it is 1.5s when skipping the first height
    /// and then increases with the increments of 200ms
    fn get_delay(&self) -> Duration {
        if self.is_endorsement() {
            ENDORSEMENT_TIMEOUT
        } else {
            // Under normal circumstances if F is the last final block, the chain
            // at this point looks as follows:
            //
            //     A <- B <- F
            //
            // We are skipping the height after A. If the next block to be N, the
            // chain will look as follows:
            //
            //     N <- . <- A <- B <- F
            //
            // The difference in heights between N and F is 4, thus the 4 below.
            min(
                MAX_SKIP_TIMEOUT,
                INITIAL_SKIP_TIMEOUT
                    + SKIP_TIMEOUT_STEP
                        * (min(
                            self.target_height
                                .saturating_sub(self.largest_final_height + 4),
                            std::u32::MAX as u64,
                        ) as u32),
            )
        }
    }

    /// Computes whether the next attestation will be an endorsement.
    ///
    /// By definition an attestation is an endorsement if the difference between
    /// the source and the destination height is exactly one.
    fn is_endorsement(&self) -> bool {
        self.target_height == self.head_height + 1
    }

    /// Given the current time, determines whether to issue an attestation.
    ///
    /// # Returns
    /// The target height for the attestation (the source height is the head
    /// height, and is thus known to the caller).
    pub fn check_attestation_creation(&mut self, now: Instant) -> Option<BlockHeight> {
        let delay = self.get_delay();
        if now >= self.timer_started + delay {
            // For the endorsements the target height must be larger than the
            // largest previously attested target height.
            let ret = if self.is_endorsement()
                && self.target_height > self.largest_attestation_height
                || !self.is_endorsement()
            {
                self.largest_attestation_height =
                    max(self.largest_attestation_height, self.target_height);
                Some(self.target_height)
            } else {
                None
            };

            self.target_height += 1;
            self.timer_started += delay;

            ret
        } else {
            None
        }
    }

    /// Updates the current head and the latest final block and restarts the timer
    pub fn update_head(
        &mut self,
        now: Instant,
        head_height: BlockHeight,
        largest_final_height: BlockHeight,
    ) {
        assert!(head_height > self.head_height);

        self.head_height = head_height;
        self.largest_final_height = largest_final_height;

        self.timer_started = now;
        self.target_height = head_height + 1;
    }
}

impl AttestationTracker {
    pub fn new() -> Self {
        Self {
            head_height: 0,
            attestations: HashMap::new(),
        }
    }

    pub fn update_head(&mut self, head_height: BlockHeight) {
        for height in self.head_height..head_height {
            self.attestations.remove(&height);
        }

        self.head_height = head_height;
    }

    pub fn track_attestation(
        &mut self,
        source_height: BlockHeight,
        target_height: BlockHeight,
        validator_ord: ValidatorOrd,
        validator_stake: Balance,
        attestation: Signature,
    ) {
        if source_height < self.head_height
            || source_height > self.head_height + MAX_HEIGHTS_TO_TRACK_AHEAD
        {
            return;
        }

        let tracker_entry = self
            .attestations
            .entry(source_height)
            .or_insert_with(|| HashMap::new())
            .entry(target_height)
            .or_insert_with(|| AttestationTrackerEntry {
                attested_stake: 0,
                attestations: HashMap::new(),
            });
        match tracker_entry.attestations.entry(validator_ord) {
            Entry::Occupied(_) => {}
            Entry::Vacant(entry) => {
                tracker_entry.attested_stake += validator_stake;
                entry.insert(attestation);
            }
        };
    }

    /// Checks whether a block at height `target_height` can be built if the
    /// previous block has height `source_height`. Only takes into consideration
    /// the heights of the attestations, but not the hash of the block.
    /// This method exists for tests, `is_ready_to_produce_block` should be used
    /// instead, which uses `self.head_height` for the source height
    pub fn is_ready_to_produce_block_internal(
        &self,
        source_height: BlockHeight,
        target_height: BlockHeight,
        total_stake: Balance,
    ) -> bool {
        self.attestations.get(&source_height).map_or(false, |map| {
            map.get(&target_height).map_or(false, |tracker_entry| {
                tracker_entry.attested_stake > total_stake * 2 / 3
            })
        })
    }

    pub fn is_ready_to_produce_block(
        &self,
        target_height: BlockHeight,
        total_stake: Balance,
    ) -> bool {
        self.is_ready_to_produce_block_internal(self.head_height, target_height, total_stake)
    }

    pub fn remove_witness_internal(
        &mut self,
        source_height: BlockHeight,
        target_height: BlockHeight,
    ) -> Vec<(ValidatorOrd, Signature)> {
        self.attestations
            .get_mut(&source_height)
            .map_or(vec![], |map| {
                map.remove(&target_height)
                    .map_or(vec![], |tracker| tracker.attestations.into_iter().collect())
            })
    }

    pub fn remove_witness(&mut self, target_height: BlockHeight) -> Vec<(ValidatorOrd, Signature)> {
        self.remove_witness_internal(self.head_height, target_height)
    }
}

#[test]
fn test_sanity_attestation_issuer() {
    const ONE_MS: Duration = Duration::from_millis(1);

    let mut now = Instant::now();
    let mut ai = AttestationIssuer::new(now);
    let mut next_height = 6;

    // Under normal circumstances when 5 is produced, 3 is final
    ai.update_head(now, 5, 3);
    assert_eq!(ai.get_delay(), ENDORSEMENT_TIMEOUT);

    now += ENDORSEMENT_TIMEOUT - ONE_MS;
    assert_eq!(ai.check_attestation_creation(now), None);

    now += ONE_MS;
    assert_eq!(ai.check_attestation_creation(now), Some(next_height));

    let mut delay = INITIAL_SKIP_TIMEOUT;
    loop {
        let break_now = if delay > MAX_SKIP_TIMEOUT {
            delay = MAX_SKIP_TIMEOUT;
            true
        } else {
            false
        };

        next_height += 1;

        now += delay - ONE_MS;
        assert_eq!(ai.check_attestation_creation(now), None);

        now += ONE_MS;
        assert_eq!(ai.check_attestation_creation(now), Some(next_height));

        if break_now {
            break;
        }

        delay += SKIP_TIMEOUT_STEP;
    }
}

#[test]
fn test_sanity_attestation_tracker() {
    const ALICE: ValidatorOrd = 0;
    const BOB: ValidatorOrd = 1;
    const CHARLIE: ValidatorOrd = 2;

    let mut at = AttestationTracker::new();

    at.update_head(1);

    at.track_attestation(1, 2, ALICE, 4, Signature::default());
    at.track_attestation(1, 3, BOB, 2, Signature::default());
    at.track_attestation(2, 3, ALICE, 4, Signature::default());

    // While there's enough stake attesting with source height 1 and enough stake
    // attesting with target height 3, there's not enough with the same source and
    // target heights, so no block shall be allowed to be produced yet
    assert!(!at.is_ready_to_produce_block(2, 7));
    assert!(!at.is_ready_to_produce_block(3, 7));

    at.track_attestation(1, 2, BOB, 2, Signature::default());
    assert!(at.is_ready_to_produce_block(2, 7));
    assert!(!at.is_ready_to_produce_block(3, 7));

    at.track_attestation(1, 3, ALICE, 4, Signature::default());
    assert!(at.is_ready_to_produce_block(3, 7));

    at.update_head(2);
    assert!(!at.is_ready_to_produce_block(3, 7));

    at.track_attestation(2, 3, CHARLIE, 1, Signature::default());
    assert!(at.is_ready_to_produce_block(3, 7));
}
