use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::runtime::HasRuntime;
use crate::core::traits::core::Async;
use crate::core::traits::packet::IbcPacket;
use crate::core::types::aliases::ClientId;

pub trait RelayContext: HasRuntime {
    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error, Runtime = Self::Runtime>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error, Runtime = Self::Runtime>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + Async;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;

    fn source_client_id(&self) -> &ClientId<Self::SrcChain, Self::DstChain>;

    fn destination_client_id(&self) -> &ClientId<Self::DstChain, Self::SrcChain>;
}
