use crate::traits::chain_types::{IbcChainContext, IbcChainTypes};
use crate::traits::core::CoreTraits;
use crate::traits::packet::IbcPacket;

pub trait RelayTypes: CoreTraits {
    type Error: CoreTraits;

    type SrcChain: IbcChainTypes<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainTypes<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + CoreTraits;
}

pub trait RelayContext: CoreTraits {
    type Error: CoreTraits;

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

pub trait RelayTypesPair: CoreTraits {
    type SrcToDestContext: RelayTypes;

    type DstToSrcContext: RelayTypes<
        SrcChain = <Self::SrcToDestContext as RelayTypes>::DstChain,
        DstChain = <Self::SrcToDestContext as RelayTypes>::SrcChain,
        Error = <Self::SrcToDestContext as RelayTypes>::Error,
    >;
}
