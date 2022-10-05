use crate::core::traits::core::Async;
use core::fmt::Debug;

#[derive(Debug, Clone)]
pub struct OfaErrorContext<Error> {
    pub error: Error,
}

impl<Error> OfaErrorContext<Error> {
    pub fn new(error: Error) -> Self {
        Self { error }
    }
}

pub trait OfaError: Async + Debug {
    fn is_retryable(&self) -> bool;

    fn max_retry_exceeded(retries: usize) -> Self;

    fn mismatch_ibc_events_count(expected: usize, actual: usize) -> Self;
}
