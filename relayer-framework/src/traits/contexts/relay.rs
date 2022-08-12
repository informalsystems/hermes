use crate::traits::contexts::chain::IbcChainContext;
use crate::traits::contexts::runtime::HasRuntime;
use crate::traits::core::Async;
use crate::traits::packet::IbcPacket;
use crate::types::aliases::ClientId;

pub trait RelayContext: HasRuntime {
    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error, Runtime = Self::Runtime>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error, Runtime = Self::Runtime>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + Async;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;

    fn source_client_id(&self) -> &ClientId<Self::SrcChain, Self::DstChain>;

    fn destination_client_id(&self) -> &ClientId<Self::DstChain, Self::SrcChain>;
}
