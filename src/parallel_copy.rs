//! Checked destruction of simultaneous local-to-local copies.
//!
//! Original locals are `0..local_count`; `local_count` is the only scratch
//! location. Scheduling is deterministic and uses one reusable scratch. The
//! validator independently replays symbols, including writes to locals absent
//! from the requested parallel assignment.

use std::collections::{BTreeMap, BTreeSet};

/// Matches the maximum number of values in a checked SSA function.
pub const MAX_LOCALS: usize = 65_536;
/// Input and retained graph bounds, checked before allocating scheduler state.
pub const MAX_PARALLEL_COPIES: usize = 65_536;
/// Includes scratch saves; the scheduler actually needs at most `3 * n / 2`.
pub const MAX_SEQUENTIAL_COPIES: usize = 131_072;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Copy {
    pub destination: usize,
    pub source: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Schedule {
    pub copies: Vec<Copy>,
    pub uses_temporary: bool,
}

fn check_limits(local_count: usize, parallel_len: usize) -> Result<(), String> {
    if local_count > MAX_LOCALS {
        return Err(format!(
            "parallel copy local limit exceeded: {local_count} > {MAX_LOCALS}"
        ));
    }
    if parallel_len > MAX_PARALLEL_COPIES {
        return Err(format!(
            "parallel copy count limit exceeded: {parallel_len} > {MAX_PARALLEL_COPIES}"
        ));
    }
    Ok(())
}

fn check_parallel_indices(local_count: usize, parallel: &[Copy]) -> Result<(), String> {
    for (index, copy) in parallel.iter().enumerate() {
        if copy.destination >= local_count || copy.source >= local_count {
            return Err(format!(
                "parallel copy {index} references a nonoriginal local"
            ));
        }
    }
    Ok(())
}

/// Schedule a simultaneous assignment, omitting self copies.
///
/// Destinations must be distinct even for self copies. Each copy is emitted
/// only when its destination is no longer needed as a source. If only cycles
/// remain, save the smallest destination and redirect its readers to scratch.
/// All loops and retained collections are bounded by the input limits; the
/// algorithm takes `O(n log n)` work and `O(n)` space, independent of the size
/// of gaps between the referenced local indices. Errors return no schedule.
pub fn schedule(local_count: usize, parallel: &[Copy]) -> Result<Schedule, String> {
    check_limits(local_count, parallel.len())?;
    check_parallel_indices(local_count, parallel)?;

    let mut pending = BTreeMap::new();
    for copy in parallel {
        if pending.insert(copy.destination, copy.source).is_some() {
            return Err(format!(
                "duplicate parallel destination {}",
                copy.destination
            ));
        }
    }
    pending.retain(|destination, source| destination != source);

    let mut readers: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (&destination, &source) in &pending {
        readers.entry(source).or_default().insert(destination);
    }
    let mut ready: BTreeSet<_> = pending
        .keys()
        .copied()
        .filter(|destination| !readers.contains_key(destination))
        .collect();
    // At most one extra save per cycle, and every cycle has at least two
    // nonself copies. The input caps bound this reservation as well.
    let mut copies = Vec::with_capacity(pending.len() + pending.len() / 2);
    let mut uses_temporary = false;
    while !pending.is_empty() {
        if let Some(destination) = ready.pop_first() {
            let source = pending
                .remove(&destination)
                .ok_or("missing ready destination")?;
            copies.push(Copy {
                destination,
                source,
            });
            let source_readers = readers.get_mut(&source).ok_or("missing source readers")?;
            source_readers.remove(&destination);
            if source_readers.is_empty() {
                readers.remove(&source);
                if pending.contains_key(&source) {
                    ready.insert(source);
                }
            }
        } else {
            let destination = *pending.first_key_value().ok_or("missing cycle")?.0;
            // An outstanding scratch reader always belongs to a component
            // with a ready destination, so scratch is free at every cycle cut.
            if readers.contains_key(&local_count) {
                return Err("scratch still in use at cycle cut".into());
            }
            copies.push(Copy {
                destination: local_count,
                source: destination,
            });
            uses_temporary = true;
            let saved_readers = readers.remove(&destination).ok_or("cycle has no readers")?;
            for reader in &saved_readers {
                *pending.get_mut(reader).ok_or("missing cycle reader")? = local_count;
            }
            readers.insert(local_count, saved_readers);
            ready.insert(destination);
        }
    }
    Ok(Schedule {
        copies,
        uses_temporary,
    })
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Symbol {
    Original(usize),
}

/// Independently prove a candidate sequence implements the parallel copies.
///
/// Every original input has its own symbol. Only modified original locals are
/// stored; omitted locals retain their original symbols by construction. The
/// final checks cover requested destinations and every other written local.
/// Scratch starts uninitialized and is unobservable after the sequence. The
/// checker accepts any equivalent sequence within the limits, without invoking
/// or reproducing the scheduler's graph algorithm.
pub fn validate(local_count: usize, parallel: &[Copy], sequential: &[Copy]) -> Result<(), String> {
    check_limits(local_count, parallel.len())?;
    if sequential.len() > MAX_SEQUENTIAL_COPIES {
        return Err(format!(
            "sequential copy count limit exceeded: {} > {MAX_SEQUENTIAL_COPIES}",
            sequential.len()
        ));
    }
    check_parallel_indices(local_count, parallel)?;
    for (index, copy) in sequential.iter().enumerate() {
        if copy.destination > local_count || copy.source > local_count {
            return Err(format!(
                "sequential copy {index} references an invalid local"
            ));
        }
    }

    let mut expected = BTreeMap::new();
    for copy in parallel {
        if expected
            .insert(copy.destination, Symbol::Original(copy.source))
            .is_some()
        {
            return Err(format!(
                "duplicate parallel destination {}",
                copy.destination
            ));
        }
    }
    let mut actual = BTreeMap::new();
    let mut scratch = None;
    for (index, copy) in sequential.iter().enumerate() {
        let value = if copy.source == local_count {
            scratch.ok_or_else(|| format!("sequential copy {index} reads uninitialized scratch"))?
        } else {
            actual
                .get(&copy.source)
                .copied()
                .unwrap_or(Symbol::Original(copy.source))
        };
        if copy.destination == local_count {
            scratch = Some(value);
        } else if value == Symbol::Original(copy.destination) {
            actual.remove(&copy.destination);
        } else {
            actual.insert(copy.destination, value);
        }
    }

    for (&destination, &value) in &expected {
        let found = actual
            .get(&destination)
            .copied()
            .unwrap_or(Symbol::Original(destination));
        if found != value {
            return Err(format!(
                "parallel destination {destination}: expected {value:?}, found {found:?}"
            ));
        }
    }
    for (&destination, &found) in &actual {
        let value = expected
            .get(&destination)
            .copied()
            .unwrap_or(Symbol::Original(destination));
        if found != value {
            return Err(format!(
                "unmentioned local {destination} was changed: found {found:?}"
            ));
        }
    }
    Ok(())
}
