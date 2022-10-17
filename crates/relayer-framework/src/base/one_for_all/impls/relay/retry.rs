use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::packet_relayers::general::retry::SupportsPacketRetry;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay: OfaBaseRelay> SupportsPacketRetry for OfaRelayWrapper<Relay> {
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Self::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        Relay::max_retry_exceeded_error(e)
    }
}
