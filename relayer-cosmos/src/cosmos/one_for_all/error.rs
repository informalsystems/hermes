use ibc_relayer_framework::one_for_all::traits::error::OfaError;

use crate::cosmos::error::Error;

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
