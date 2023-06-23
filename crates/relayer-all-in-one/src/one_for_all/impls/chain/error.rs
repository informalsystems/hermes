use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components_extra::relay::impls::packet_relayers::retry::SupportsPacketRetry;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay: OfaRelay> SupportsPacketRetry for OfaRelayWrapper<Relay> {
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Self::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        Relay::max_retry_exceeded_error(e)
    }
}

impl<Chain: OfaChain> HasErrorType for OfaChainWrapper<Chain> {
    type Error = Chain::Error;
}
