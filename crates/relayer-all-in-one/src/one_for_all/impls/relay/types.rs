use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay: OfaRelay> HasErrorType for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    type Error = Relay::Error;
}

impl<Relay> HasRuntime for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    type Runtime = Relay::Runtime;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Relay::Error {
        Relay::runtime_error(e)
    }
}

impl<Relay> HasRelayChains for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    type Packet = <Relay::SrcChain as OfaChainTypes>::OutgoingPacket;

    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

    fn src_chain_error(e: <Self::SrcChain as HasErrorType>::Error) -> Self::Error {
        Relay::src_chain_error(e)
    }

    fn dst_chain_error(e: <Self::DstChain as HasErrorType>::Error) -> Self::Error {
        Relay::dst_chain_error(e)
    }

    fn src_chain(&self) -> &Self::SrcChain {
        self.relay.src_chain()
    }

    fn dst_chain(&self) -> &Self::DstChain {
        self.relay.dst_chain()
    }

    fn src_client_id(&self) -> &<Relay::SrcChain as OfaChainTypes>::ClientId {
        self.relay.src_client_id()
    }

    fn dst_client_id(&self) -> &<Relay::DstChain as OfaChainTypes>::ClientId {
        self.relay.dst_client_id()
    }
}
