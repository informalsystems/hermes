use crate::traits::core::Async;
use core::fmt::Debug;

pub trait OfaError: Async + Debug {
    fn is_retryable(&self) -> bool;

    fn max_retry_exceeded(retries: usize) -> Self;

    fn mismatch_ibc_events_count(expected: usize, actual: usize) -> Self;
}
