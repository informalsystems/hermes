use crate::impls::packet_relayers::retry::{MaxRetryExceeded, RetryableError};
use crate::one_for_all::traits::error::OfaError;
use crate::traits::ibc_message_sender::MismatchIbcEventsCountError;

pub struct OfaHasError<Error> {
    pub error: Error,
}

impl<Error> OfaHasError<Error> {
    pub fn new(error: Error) -> Self {
        Self { error }
    }
}

impl<Error: OfaError> RetryableError for OfaHasError<Error> {
    fn is_retryable(&self) -> bool {
        self.error.is_retryable()
    }
}

impl<Error> From<Error> for OfaHasError<Error> {
    fn from(error: Error) -> Self {
        Self { error }
    }
}

impl<Error: OfaError> From<MismatchIbcEventsCountError> for OfaHasError<Error> {
    fn from(e: MismatchIbcEventsCountError) -> Self {
        Self::new(Error::mismatch_ibc_events_count(e.expected, e.actual))
    }
}

impl<Error: OfaError> From<MaxRetryExceeded> for OfaHasError<Error> {
    fn from(e: MaxRetryExceeded) -> Self {
        Self::new(Error::max_retry_exceeded(e.retries))
    }
}
