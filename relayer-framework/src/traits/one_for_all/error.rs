use crate::traits::core::Async;

pub trait OfaError: Async {
    fn mismatch_ibc_events_count(expected: usize, actual: usize) -> Self;
}
