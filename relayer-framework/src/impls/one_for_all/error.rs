use crate::traits::ibc_message_sender::MismatchIbcEventsCountError;
use crate::traits::one_for_all::error::OfaError;

pub struct OfaErrorContext<Error> {
    pub error: Error,
}

impl<Error> OfaErrorContext<Error> {
    pub fn new(error: Error) -> Self {
        Self { error }
    }
}

impl<Error> From<Error> for OfaErrorContext<Error> {
    fn from(error: Error) -> Self {
        Self { error }
    }
}

impl<Error: OfaError> From<MismatchIbcEventsCountError> for OfaErrorContext<Error> {
    fn from(e: MismatchIbcEventsCountError) -> Self {
        Self::new(Error::mismatch_ibc_events_count(e.expected, e.actual))
    }
}
