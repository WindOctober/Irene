use super::*;

fn satisfied(rows: &[Vec<usize>], columns: usize, value: usize) -> bool {
    rows.iter().all(|row| {
        !row.iter()
            .fold(false, |a, &c| a ^ (c == columns || value & (1 << c) != 0))
    })
}

#[test]
fn every_small_augmented_system_preserves_all_solutions() {
    for columns in 0..=3 {
        let possibilities = 1usize << (columns + 1);
        for code in 0..possibilities.pow(3) {
            let rows = (0..3)
                .map(|i| {
                    let mask = (code / possibilities.pow(i)) % possibilities;
                    (0..=columns)
                        .filter(|c| mask & (1 << c) != 0)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let reduced = packed_reduce(&rows, columns);
            assert_eq!(
                reduced.is_none(),
                (0..1 << columns).all(|v| !satisfied(&rows, columns, v))
            );
            if let Some(mut reduced) = reduced {
                for v in 0..1 << columns {
                    assert_eq!(
                        satisfied(&rows, columns, v),
                        satisfied(&reduced, columns, v)
                    );
                }
                reduced.sort();
                let mut reversed = rows.clone();
                reversed.reverse();
                let mut other = packed_reduce(&reversed, columns).unwrap();
                other.sort();
                assert_eq!(reduced, other);
            }
        }
    }
}

#[test]
fn packed_padding_and_last_constant_column_do_not_become_variables() {
    for columns in [1, 2, 63, 64, 65, 127, 128, 129] {
        let mut rows = (0..columns)
            .map(|c| {
                if c % 3 == 0 {
                    vec![c, columns]
                } else {
                    vec![c]
                }
            })
            .collect::<Vec<_>>();
        rows.push(vec![]);
        let mut reduced = packed_reduce(&rows, columns).unwrap();
        reduced.sort();
        let mut expected = rows[..columns].to_vec();
        expected.sort();
        assert_eq!(reduced, expected);
        rows.push(vec![0]);
        assert!(packed_reduce(&rows, columns).is_none());
    }
    assert_eq!(packed_reduce(&[], 0), Some(vec![]));
    assert_eq!(packed_reduce(&[vec![], vec![]], 0), Some(vec![]));
    assert!(packed_reduce(&[vec![0]], 0).is_none());
}

#[test]
fn disconnected_components_match_one_augmented_matrix() {
    let columns = 256;
    let mut rows = Vec::new();
    for i in 0..64 {
        // Interleaved global columns require local->global ordering to survive.
        let a = i;
        let b = i + 64;
        let c = i + 128;
        let d = i + 192;
        rows.extend([vec![a, b, columns], vec![b, c], vec![c, d, columns]]);
    }
    let mut components = packed_reduce(&rows, columns).unwrap();
    components.sort();
    let mut whole = block(
        &rows,
        &(0..rows.len()).collect::<Vec<_>>(),
        &(0..columns).collect::<Vec<_>>(),
        columns,
        &mut vec![0; columns],
    )
    .unwrap();
    whole.sort();
    assert_eq!(components, whole);
    rows.reverse();
    let mut reversed = packed_reduce(&rows, columns).unwrap();
    reversed.sort();
    assert_eq!(components, reversed);
    rows.extend([vec![3], vec![3, columns]]);
    assert!(packed_reduce(&rows, columns).is_none());
}
