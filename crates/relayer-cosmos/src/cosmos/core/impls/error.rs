use crate::cosmos::core::error::Error;
use ibc_relayer_framework::base::one_for_all::traits::error::OfaError;

impl OfaError for Error {
    fn is_retryable(&self) -> bool {
        false
    }

    fn max_retry_exceeded(retries: usize) -> Self {
        Error::max_retry(retries)
    }

    fn mismatch_ibc_events_count(expected: usize, actual: usize) -> Self {
        Error::mismatch_ibc_events_count(expected, actual)
    }
}
