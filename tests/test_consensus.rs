use rand::seq::SliceRandom;
use rand::{thread_rng, Rng};
use consensus::{AttestationIssuer, AttestationTracker, MAX_HEIGHTS_TO_TRACK_AHEAD};
use types::{Balance, BlockHash, BlockHeight, Signature, ValidatorOrd};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryInto;
use std::time::{Duration, Instant};

fn get_msg_delivery_time(now: Instant, gst: Instant, delta: usize, step: usize) -> Instant {
    std::cmp::max(now, gst)
        + Duration::from_millis((thread_rng().gen_range(step, delta) / step * step) as u64)
}

fn get_block_producer(height: BlockHeight, num_validators: usize) -> usize {
    height as usize % num_validators
}

/// Tracks sufficient information to detect attestations that violate attestation
/// conditions.
///
/// Specifically, for each validator maintains a datastructure that for each height
/// `h` can return an attestation with the furthest ahead target height that
/// surrounds `h` which allows to detect non-endorsing attestations that surround
/// an endorsement.
/// Also maintains a set of endorsements to detect double-endorsing.
///
/// `Value` is what needs to be returned to the caller when slashable behavior
/// is detected. Is a template parameter to simplify testing.
pub struct SlashingTracker<Value> {
    head_height: BlockHeight,

    /// For each validator ordinal, maps the `source_height` to the `prev_block_hash`
    /// and the value.
    endorsements: HashMap<ValidatorOrd, BTreeMap<BlockHeight, (BlockHash, Value)>>,
    /// For each validator ordinal, maps the `source_height` to the furthest
    /// `target_height` with the same or lower source height.
    /// It maintains the invariant that no two consecutive entries overlap.
    furthest_target_height: HashMap<ValidatorOrd, BTreeMap<BlockHeight, (BlockHeight, Value)>>,
}

impl<Value: Clone> SlashingTracker<Value> {
    pub fn new() -> Self {
        Self {
            head_height: 0,
            endorsements: HashMap::new(),
            furthest_target_height: HashMap::new(),
        }
    }

    pub fn update_head(&mut self, head_height: BlockHeight) {
        self.head_height = head_height;
    }

    /// Tracks an endorsement. Ensures that
    /// - There's no endorsement with the same source_height and different prev_hash
    /// - There's no non-endorsing attestation surrounding the `source_height`
    pub fn track_endorsement(
        &mut self,
        validator_ord: ValidatorOrd,
        prev_block_hash: BlockHash,
        source_height: BlockHeight,
        value: Value,
    ) -> Option<(Value, Value)> {
        if let Some((other_prev_block_hash, other_value)) = self
            .endorsements
            .get(&validator_ord)
            .and_then(|tree| tree.get(&source_height))
        {
            if other_prev_block_hash != &prev_block_hash {
                return Some((value, other_value.clone()));
            }
        }

        if let Some((_, (furthest_target_height, other_value))) = self
            .furthest_target_height
            .get(&validator_ord)
            .and_then(|tree| tree.range(..source_height).rev().next())
        {
            if *furthest_target_height > source_height {
                return Some((value, other_value.clone()));
            }
        }

        self.endorsements
            .entry(validator_ord)
            .or_insert_with(|| BTreeMap::new())
            .insert(source_height, (prev_block_hash, value));

        None
    }

    /// Tracks a non-endorsing attestation
    /// Ensures that there's no endorsement surrounded by the new attestation
    pub fn track_non_endorsing_attestation(
        &mut self,
        validator_ord: ValidatorOrd,
        source_height: BlockHeight,
        target_height: BlockHeight,
        value: Value,
    ) -> Option<(Value, Value)> {
        assert!(target_height > source_height + 1);

        if let Some((_, (_, other_value))) = self
            .endorsements
            .get(&validator_ord)
            .and_then(|tree| tree.range(source_height + 1..target_height).next())
        {
            return Some((value, other_value.clone()));
        }

        let tree = self
            .furthest_target_height
            .entry(validator_ord)
            .or_insert_with(|| BTreeMap::new());

        // Remove entries fully surrounded by the new entry
        let mut to_remove = vec![];
        for (key, (other_target_height, _)) in tree.range(source_height..) {
            if *other_target_height <= target_height {
                to_remove.push(*key);
            } else {
                break;
            }
        }

        for key in to_remove.into_iter() {
            tree.remove(&key);
        }

        // Only insert if the entry with the same or preceding key isn't having
        // bigger target_height
        if tree
            .range(..=source_height)
            .rev()
            .next()
            .map_or(true, |(_, (other_target_height, _))| {
                *other_target_height < target_height
            })
        {
            tree.insert(source_height, (target_height, value));
        }

        None
    }
}

/// For various settings of time to global stabilization time and message delays
/// instantiates 10 validators, and simulates attestation and block messages
/// between them. Makes sure that a finalized block at height 100 or above gets
/// produced.
/// Also ensures that no attestation created is treated by the SlashingTracker
/// as malicious.
#[test]
fn test_fuzzy_liveness() {
    #[cfg(not(feature = "long_fuzz"))]
    const NUM_ITERS: usize = 1;
    #[cfg(feature = "long_fuzz")]
    const NUM_ITERS: usize = 50;

    const NUM_VALIDATORS: usize = 10;
    const STEP: usize = 10;
    const TARGET_HEIGHT: BlockHeight = 100;

    for time_to_gst in &[0, 100000] {
        for delta in &[100, 300, 1100, 2200] {
            for _iter in 0..NUM_ITERS {
                println!(
                    "Starting iteration. Time to GST: {}, delta: {}",
                    time_to_gst, delta
                );
                let t0 = Instant::now();
                let gst = t0 + Duration::from_millis(*time_to_gst as u64);

                let mut validators = (0..NUM_VALIDATORS)
                    .map(|validator_ord| {
                        (
                            validator_ord,
                            AttestationIssuer::new(t0),
                            AttestationTracker::new(),
                            0,
                            0,
                        )
                    })
                    .collect::<Vec<_>>();

                let mut st = SlashingTracker::new();

                let mut now = t0;
                let mut attestation_messages = HashMap::new();
                let mut block_messages = HashMap::new();
                let mut done = false;
                let mut height_to_consecutive = HashMap::new();
                let mut height_to_last_final = HashMap::new();

                height_to_consecutive.insert(0, 0);
                height_to_last_final.insert(0, 0);

                while !done {
                    now += Duration::from_millis(STEP as u64);

                    assert!(now < t0 + Duration::from_secs(60 * 10));

                    for (validator_ord, ai, _, head_height, _) in validators.iter_mut() {
                        if let Some(target_height) = ai.check_attestation_creation(now) {
                            let target_ord = get_block_producer(target_height, NUM_VALIDATORS);
                            let msg = (*head_height, target_height, *validator_ord, target_ord);

                            // Make sure the attestation is not recognized as malicious
                            if target_height == *head_height + 1 {
                                assert!(st
                                    .track_endorsement(
                                        (*validator_ord).try_into().unwrap(),
                                        BlockHash([0; 32]),
                                        *head_height,
                                        0
                                    )
                                    .is_none());
                            } else {
                                assert!(st
                                    .track_non_endorsing_attestation(
                                        (*validator_ord).try_into().unwrap(),
                                        *head_height,
                                        target_height,
                                        0
                                    )
                                    .is_none());
                            }

                            attestation_messages
                                .entry(get_msg_delivery_time(now, gst, *delta, STEP))
                                .or_insert_with(|| vec![])
                                .push(msg);
                        }
                    }

                    for (source_height, target_height, source_ord, target_ord) in
                        attestation_messages.remove(&now).unwrap_or_else(|| vec![])
                    {
                        let (_, _, tracker, _, largest_produced_height) =
                            validators.get_mut(target_ord).unwrap();

                        tracker.track_attestation(
                            source_height.try_into().unwrap(),
                            target_height.try_into().unwrap(),
                            source_ord.try_into().unwrap(),
                            1,
                            Signature::default(),
                        );

                        if get_block_producer(target_height, NUM_VALIDATORS) == target_ord
                            && tracker
                                .is_ready_to_produce_block(target_height, NUM_VALIDATORS as Balance)
                            && target_height > *largest_produced_height
                        {
                            let consecutive = *height_to_consecutive.get(&source_height).unwrap();
                            let last_final = *height_to_last_final.get(&source_height).unwrap();

                            let (consecutive, last_final) = if target_height == source_height + 1 {
                                (
                                    consecutive + 1,
                                    if consecutive > 0 {
                                        source_height - 1
                                    } else {
                                        last_final
                                    },
                                )
                            } else {
                                (0, last_final)
                            };

                            height_to_consecutive.insert(target_height, consecutive);
                            height_to_last_final.insert(target_height, last_final);

                            *largest_produced_height = target_height;

                            for recepient in 0..NUM_VALIDATORS {
                                block_messages
                                    .entry(get_msg_delivery_time(now, gst, *delta, STEP))
                                    .or_insert_with(|| vec![])
                                    .push((target_height, recepient));
                            }
                        }
                    }

                    for (block_height, validator_ord) in
                        block_messages.remove(&now).unwrap_or_else(|| vec![])
                    {
                        let (_, ai, at, head_height, _) =
                            validators.get_mut(validator_ord).unwrap();

                        let last_final = *height_to_last_final.get(&block_height).unwrap();
                        if block_height > *head_height {
                            *head_height = block_height;
                            ai.update_head(now, block_height, last_final);
                            at.update_head(block_height);
                        }

                        if last_final >= TARGET_HEIGHT {
                            done = true;
                        }
                    }
                }
            }
        }
    }
}

/// For a set of block producers creates random attestations, and for as long as
/// such attestations are not flagged by the SlashingTracker, adds them to an
/// AttestationsTracker, and simulates block creation whenever the attestations
/// tracker has enough attestations.
/// At the end ensures that for each final block no block was created with a
/// higher height that doesn't have the final block in its ancestry.
#[test]
fn test_fuzzy_safety() {
    #[cfg(not(feature = "long_fuzz"))]
    const NUM_ITERS: usize = 5;
    #[cfg(feature = "long_fuzz")]
    const NUM_ITERS: usize = 100;
    const NUM_STEPS_PER_ITER: usize = 3000;

    let hash = |height: BlockHeight, mut prev_hash: BlockHash| -> BlockHash {
        use sha2::Digest;
        prev_hash.0[0] = height.try_into().unwrap();
        BlockHash(sha2::Sha256::digest(&prev_hash.0).into())
    };

    let mut good_iters = 0;

    while good_iters < NUM_ITERS {
        println!("Iteration");

        // Only count iterations that produced at least five final blocks
        let mut num_final_blocks = 0;

        let num_validators = thread_rng().gen_range(4, 8);
        let stakes = (0..num_validators)
            .map(|_| thread_rng().gen_range(10, 30) as Balance)
            .collect::<Vec<_>>();
        let total_stake: Balance = stakes.iter().sum();

        let mut malicious_validators = 0;
        let mut malicious_stake = 0;

        while (malicious_stake + stakes[malicious_validators]) * 3 < total_stake {
            malicious_stake += stakes[malicious_validators];
            malicious_validators += 1;
        }

        let mut at = AttestationTracker::new();
        let mut st = SlashingTracker::new();

        let mut blocks = vec![hash(1, BlockHash([0; 32]))];
        let mut block_to_height = HashMap::new();
        let mut height_to_block = HashMap::new();
        let mut block_to_prev = HashMap::new();
        let mut sent_attestations = HashSet::new();
        block_to_height.insert(blocks[0].clone(), 1 as BlockHeight);
        height_to_block.insert(1 as BlockHeight, blocks[0].clone());

        at.update_head(1);
        st.update_head(1);

        for _step in 0..NUM_STEPS_PER_ITER {
            let validator_ord = thread_rng().gen_range(0, num_validators);

            let prev_block_hash = blocks.choose(&mut thread_rng()).unwrap().clone();
            let source_height = *block_to_height.get(&prev_block_hash).unwrap();
            if source_height >= MAX_HEIGHTS_TO_TRACK_AHEAD - 2 {
                continue;
            }

            let want_endorsement = thread_rng().gen_range(0, 10) != 1;
            let mut attempts = 0;

            let target_height = loop {
                attempts += 1;
                if attempts > 20 {
                    break None;
                }
                let target_height = if want_endorsement {
                    source_height + 1
                } else {
                    thread_rng().gen_range(
                        source_height + 1,
                        std::cmp::min(MAX_HEIGHTS_TO_TRACK_AHEAD, source_height + 6),
                    )
                };

                let is_slashed = if target_height == source_height + 1 {
                    st.track_endorsement(validator_ord, prev_block_hash.clone(), source_height, 0)
                        .is_some()
                } else {
                    st.track_non_endorsing_attestation(
                        validator_ord,
                        source_height,
                        target_height,
                        0,
                    )
                    .is_some()
                };

                // Make 1/3 of the validators commit slashable acts
                if is_slashed && validator_ord >= malicious_validators as u16 {
                    continue;
                }

                if sent_attestations.contains(&(
                    prev_block_hash.clone(),
                    target_height,
                    validator_ord,
                )) {
                    continue;
                } else {
                    sent_attestations.insert((
                        prev_block_hash.clone(),
                        target_height,
                        validator_ord,
                    ));
                }

                break Some(target_height);
            };

            let target_height = match target_height {
                Some(x) => x,
                None => continue,
            };

            at.track_attestation(
                source_height,
                target_height,
                validator_ord,
                stakes[validator_ord as usize],
                Signature::default(),
            );

            if at.is_ready_to_produce_block_internal(source_height, target_height, total_stake) {
                at.remove_witness_internal(source_height, target_height);

                let prev_hash = height_to_block.get(&source_height).unwrap();
                let current_hash = hash(target_height, prev_hash.clone());
                block_to_prev.insert(current_hash.clone(), prev_hash.clone());
                block_to_height.insert(current_hash.clone(), target_height);
                height_to_block.insert(target_height, current_hash.clone());
                blocks.push(current_hash);
            }
        }

        for block in blocks.iter() {
            let height = *block_to_height.get(block).unwrap();
            if height == 1 {
                continue;
            }
            let prev = block_to_prev.get(block).unwrap();
            let prev_height = *block_to_height.get(prev).unwrap();
            if prev_height == 1 || height != prev_height + 1 {
                continue;
            }
            let prev_prev = block_to_prev.get(prev).unwrap();
            let prev_prev_height = *block_to_height.get(prev_prev).unwrap();

            if prev_height != prev_prev_height + 1 {
                continue;
            }

            num_final_blocks += 1;

            for other_block in blocks.iter() {
                let other_height = *block_to_height.get(other_block).unwrap();
                if other_height > prev_prev_height {
                    // This block must be on the same chain as prev_prev
                    let mut cur = other_block.clone();
                    let mut heights = vec![other_height];

                    loop {
                        // prev_prev is on chain, great
                        if &cur == prev_prev {
                            break;
                        }

                        let cur_height = *block_to_height.get(&cur).unwrap();
                        heights.push(cur_height);
                        if cur_height < prev_prev_height {
                            println!("{} not in {:?}", prev_prev_height, heights);
                            assert!(false);
                        }

                        cur = block_to_prev.get(&cur).unwrap().clone();
                    }
                }
            }
        }

        if num_final_blocks >= 5 {
            good_iters += 1;
        }
    }
}
