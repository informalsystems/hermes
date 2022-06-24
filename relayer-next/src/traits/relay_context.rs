use super::chain_context::IbcChainContext;

use crate::traits::packet::IbcPacket;

pub trait RelayContext: Sized + Send + Sync + 'static {
    type Error;

    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain>;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;
}

pub trait RelayContextPair {
    type SrcContext: RelayContext;

    type DstContext: RelayContext<
        SrcChain = <Self::SrcContext as RelayContext>::DstChain,
        DstChain = <Self::SrcContext as RelayContext>::SrcChain,
        Error = <Self::SrcContext as RelayContext>::Error,
    >;

    fn source_context(&self) -> &Self::SrcContext;

    fn destination_context(&self) -> &Self::DstContext;
}
