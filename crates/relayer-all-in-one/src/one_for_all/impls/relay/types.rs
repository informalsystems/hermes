use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::relay::traits::types::HasRelayTypes;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;

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
    type Runtime = OfaRuntimeWrapper<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Relay::Error {
        Relay::runtime_error(e)
    }
}

impl<Relay> HasRelayTypes for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

    type Packet = Relay::Packet;

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

    fn src_client_id(&self) -> &<Relay::SrcChain as OfaChain>::ClientId {
        self.relay.src_client_id()
    }

    fn dst_client_id(&self) -> &<Relay::DstChain as OfaChain>::ClientId {
        self.relay.dst_client_id()
    }
}
