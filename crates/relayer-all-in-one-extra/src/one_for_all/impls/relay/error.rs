use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::full::relay::impls::packet_relayers::retry::SupportsPacketRetry;

impl<Relay: OfaFullRelay> SupportsPacketRetry for OfaRelayWrapper<Relay> {
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Self::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        Relay::max_retry_exceeded_error(e)
    }
}
