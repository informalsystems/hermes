use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;

impl<Relay: OfaBaseRelay> HasErrorType for OfaRelayWrapper<Relay> {
    type Error = Relay::Error;
}

impl<Relay: OfaBaseRelay> HasRuntime for OfaRelayWrapper<Relay> {
    type Runtime = OfaRuntimeWrapper<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Relay::Error {
        Relay::runtime_error(e)
    }
}

impl<Relay: OfaBaseRelay> HasRelayTypes for OfaRelayWrapper<Relay> {
    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

    type Packet = Relay::Packet;

    fn src_chain_error(e: <Self::SrcChain as HasErrorType>::Error) -> Self::Error {
        Relay::src_chain_error(e)
    }

    fn dst_chain_error(e: <Self::DstChain as HasErrorType>::Error) -> Self::Error {
        Relay::dst_chain_error(e)
    }

    fn source_chain(&self) -> &Self::SrcChain {
        self.relay.src_chain()
    }

    fn destination_chain(&self) -> &Self::DstChain {
        self.relay.dst_chain()
    }

    fn source_client_id(&self) -> &<Relay::SrcChain as OfaChainTypes>::ClientId {
        self.relay.src_client_id()
    }

    fn destination_client_id(&self) -> &<Relay::DstChain as OfaChainTypes>::ClientId {
        self.relay.dst_client_id()
    }
}
