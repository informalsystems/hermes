use crate::core::impls::packet_relayers::retry::{MaxRetryExceeded, RetryableError};
use crate::core::traits::ibc_message_sender::MismatchIbcEventsCountError;

pub trait AfoError:
    From<MismatchIbcEventsCountError> + From<MaxRetryExceeded> + RetryableError
{
}

impl<Error> AfoError for Error where
    Error: From<MismatchIbcEventsCountError> + From<MaxRetryExceeded> + RetryableError
{
}
