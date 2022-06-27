use crate::traits::chain_types::{IbcChainContext, IbcChainTypes};
use crate::traits::core::{Async, ErrorContext};
use crate::traits::packet::IbcPacket;

pub trait RelayTypes: ErrorContext {
    type SrcChain: IbcChainTypes<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainTypes<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + Async;
}

pub trait RelayContext: ErrorContext {
    type RelayTypes: RelayTypes<Error = Self::Error>;

    type SrcChainContext: IbcChainContext<
        <Self::RelayTypes as RelayTypes>::DstChain,
        IbcChainTypes = <Self::RelayTypes as RelayTypes>::SrcChain,
        Error = Self::Error,
    >;

    type DstChainContext: IbcChainContext<
        <Self::RelayTypes as RelayTypes>::SrcChain,
        IbcChainTypes = <Self::RelayTypes as RelayTypes>::DstChain,
        Error = Self::Error,
    >;

    fn source_context(&self) -> &Self::SrcChainContext;

    fn destination_context(&self) -> &Self::DstChainContext;
}

pub trait RelayTypesPair: Async {
    type SrcToDestContext: RelayTypes;

    type DstToSrcContext: RelayTypes<
        SrcChain = <Self::SrcToDestContext as RelayTypes>::DstChain,
        DstChain = <Self::SrcToDestContext as RelayTypes>::SrcChain,
        Error = <Self::SrcToDestContext as ErrorContext>::Error,
    >;
}
