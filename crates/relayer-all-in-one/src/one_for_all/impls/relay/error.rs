use ibc_relayer_components_extra::relay::impls::packet_relayers::retry::SupportsPacketRetry;

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> SupportsPacketRetry for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Relay::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Relay::Error) -> Relay::Error {
        Relay::max_retry_exceeded_error(e)
    }
}
