//! Scoped, cooperative deadline for an optional symbolic proof attempt.
//! Expiry is refusal, never a semantic fact. Reducers may stop only between
//! complete rewrites; the enclosing attempt discards any unfinished result.
use std::cell::Cell;
use std::time::{Duration, Instant};

thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

pub(crate) fn expired() -> bool {
    DEADLINE.with(|slot| slot.get().is_some_and(|end| Instant::now() >= end))
}

pub(crate) fn within<T>(budget: Duration, attempt: impl FnOnce() -> T) -> Option<T> {
    struct Restore(Option<Instant>);
    impl Drop for Restore {
        fn drop(&mut self) {
            DEADLINE.with(|slot| slot.set(self.0));
        }
    }
    let end = Instant::now()
        .checked_add(budget)
        .expect("finite proof budget");
    let previous = DEADLINE.with(|slot| {
        let previous = slot.get();
        slot.set(Some(previous.map_or(end, |outer| outer.min(end))));
        previous
    });
    let _restore = Restore(previous);
    if expired() {
        return None;
    }
    let result = attempt();
    (!expired()).then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expiry_does_not_escape_attempt_or_extend_outer_deadline() {
        assert_eq!(
            within(Duration::ZERO, || panic!("expired attempt ran")),
            None::<()>
        );
        assert!(!expired());
        within(Duration::from_secs(1), || {
            let outer = DEADLINE.with(Cell::get);
            within(Duration::from_secs(60), || {
                assert_eq!(DEADLINE.with(Cell::get), outer)
            });
            assert_eq!(within(Duration::ZERO, || 1), None);
            assert!(!expired());
        })
        .unwrap();
        assert_eq!(within(Duration::from_secs(1), || 42), Some(42));
        assert!(!expired());
    }

    #[test]
    fn reducer_expiry_retains_the_summand_and_executor_refuses_partial_programs() {
        use crate::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};
        let p = crate::frontend::openqasm3::parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; h q;",
            "deadline.qasm",
        )
        .unwrap();
        let output = OutputSelection::new(
            [crate::ir::Qubit {
                register: p.quantum_registers[0].id,
                index: 0,
            }],
            [],
        );
        let config = ExecutionConfig::all_symbolic();
        let hps = execute(&p, &config, &output).unwrap();
        let mut component = hps.components[0].clone();
        within(Duration::from_secs(1), || {
            DEADLINE.with(|slot| slot.set(Some(Instant::now())));
            assert!(crate::symbolic::optimize::reduce_path_sums(
                &mut component,
                false
            ));
            assert_eq!(component, hps.components[0]);
            assert_eq!(
                execute(&p, &config, &output),
                Err(SymbolicError::TimeBudget)
            );
        });
        assert_eq!(execute(&p, &config, &output).unwrap(), hps);
    }

    #[test]
    fn unfinished_result_is_discarded_and_unwind_restores_scope() {
        assert_eq!(
            within(Duration::from_secs(1), || {
                DEADLINE.with(|slot| slot.set(Some(Instant::now())));
                42
            }),
            None
        );
        let _ = std::panic::catch_unwind(|| within(Duration::from_secs(1), || panic!("test")));
        assert!(!expired());
    }
}
