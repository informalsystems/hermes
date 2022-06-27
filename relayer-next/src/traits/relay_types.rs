use crate::traits::chain_types::IbcChainContext;
use crate::traits::core::{Async, ErrorContext};
use crate::traits::packet::IbcPacket;

pub trait RelayContext: ErrorContext {
    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + Async;

    fn source_context(&self) -> &Self::SrcChain;

    fn destination_context(&self) -> &Self::DstChain;
}

pub trait RelayContextPair: Async {
    type SrcToDestContext: RelayContext;

    type DstToSrcContext: RelayContext<
        SrcChain = <Self::SrcToDestContext as RelayContext>::DstChain,
        DstChain = <Self::SrcToDestContext as RelayContext>::SrcChain,
        Error = <Self::SrcToDestContext as ErrorContext>::Error,
    >;
}
