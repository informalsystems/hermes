use ibc_relayer_components::relay::components::create_client::InjectMissingCreateClientEventError;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> InjectMissingCreateClientEventError<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_create_client_event_error(
        src_chain: &OfaChainWrapper<Relay::SrcChain>,
        dst_chain: &OfaChainWrapper<Relay::DstChain>,
    ) -> Self::Error {
        Relay::missing_src_create_client_event_error(&src_chain.chain, &dst_chain.chain)
    }
}

impl<Relay> InjectMissingCreateClientEventError<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_create_client_event_error(
        dst_chain: &OfaChainWrapper<Relay::DstChain>,
        src_chain: &OfaChainWrapper<Relay::SrcChain>,
    ) -> Self::Error {
        Relay::missing_dst_create_client_event_error(&dst_chain.chain, &src_chain.chain)
    }
}
