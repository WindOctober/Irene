//! Measurement-feedback joins over LOCAL branch groups, not whole HPS states.

use std::collections::BTreeMap;

use crate::ir::ClassicalBit;
use crate::symbolic::{Component, HistoryEntry};

use super::{
    collapse_local_history, local_history::normalize_feedback_branch,
    merge::histories_are_orthogonal, merge_components,
};

/// Called after all successors return to a common boundary and the backward
/// slice removes retired controls. Other components need not agree or be absent.
/// The event slot and preceding history identify a local measurement sector;
/// unlike grouping by the last `if`, this also reunites successors after several
/// sequential uses of one result. Prefix equality only selects candidates, NOT
/// the proof: exact HPS normalization, ray equality, weights and orthogonality
/// before AND after against outsiders are all independently required.
pub(crate) fn merge_feedback_groups(
    components: Vec<Component>,
    retired: &[ClassicalBit],
) -> Vec<Component> {
    if components.len() < 2 || components.len() > 32 {
        return components;
    }
    let mut current: Vec<_> = components.into_iter().map(Some).collect();
    for bit in retired {
        let mut groups: BTreeMap<(usize, Vec<HistoryEntry>), Vec<usize>> = BTreeMap::new();
        for (index, component) in current.iter().enumerate() {
            let Some(component) = component else { continue };
            if component.output.classical.contains_key(bit) {
                continue;
            }
            let event =
                component.output.history.iter().rposition(
                    |h| matches!(h, HistoryEntry::Write { target, .. } if target == bit),
                );
            if let Some(event) = event {
                groups
                    .entry((event, component.output.history[..event].to_vec()))
                    .or_default()
                    .push(index);
            }
        }
        for indices in groups.values().filter(|indices| indices.len() >= 2) {
            let originals: Vec<_> = indices
                .iter()
                .map(|i| current[*i].as_ref().unwrap())
                .collect();
            let outsiders: Vec<_> = current
                .iter()
                .enumerate()
                .filter(|(i, _)| !indices.contains(i))
                .filter_map(|(_, c)| c.as_ref())
                .collect();
            if !pairwise_orthogonal(&originals)
                || !originals.iter().all(|c| isolated_from(c, &outsiders))
            {
                continue;
            }
            let mut normalized: Vec<_> = originals.iter().map(|c| (*c).clone()).collect();
            if !normalized.iter_mut().all(normalize_feedback_branch)
                || !pairwise_orthogonal(&normalized.iter().collect::<Vec<_>>())
            {
                continue;
            }
            // Compare live quantum AND classical outputs, guards and full
            // input-dependent phase; add density weights, not amplitudes.
            let merged = merge_components(normalized.clone());
            let [mut representative]: [Component; 1] = match merged.try_into() {
                Ok(one) => one,
                Err(_) => continue,
            };
            collapse_local_history(&mut representative);
            if !isolated_from(&representative, &outsiders) {
                // Keep common constant environment labels if erasing them
                // would collide with an outside group. They do not change this
                // sector's self-density, but can preserve sector separation.
                let mut labels = Vec::new();
                for (i, h) in normalized[0].output.history.iter().enumerate() {
                    let value = h.value();
                    if (value.is_zero() || value.is_one())
                        && normalized
                            .iter()
                            .all(|c| c.output.history.get(i) == Some(h))
                    {
                        labels.push(h.clone());
                    }
                }
                labels.extend(representative.output.history);
                representative.output.history = labels;
                if !isolated_from(&representative, &outsiders) {
                    continue;
                }
            }
            for index in indices {
                current[*index] = None;
            }
            current[indices[0]] = Some(representative);
        }
    }
    current.into_iter().flatten().collect()
}

fn isolated_from(component: &Component, outsiders: &[&Component]) -> bool {
    outsiders
        .iter()
        .all(|outside| histories_are_orthogonal(&component.output.history, &outside.output.history))
}

fn pairwise_orthogonal(group: &[&Component]) -> bool {
    (0..group.len()).all(|i| {
        (i + 1..group.len())
            .all(|j| histories_are_orthogonal(&group[i].output.history, &group[j].output.history))
    })
}

#[cfg(test)]
mod tests;
