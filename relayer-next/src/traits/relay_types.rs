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
    type RelayTypes: RelayTypes;

    type SrcChain: IbcChainContext<<Self::RelayTypes as RelayTypes>::DstChain>;

    type DstChain: IbcChainContext<<Self::RelayTypes as RelayTypes>::SrcChain>;

    fn source_context(&self) -> &Self::SrcChain;

    fn destination_context(&self) -> &Self::DstChain;
}

pub trait RelayTypesPair: CoreTraits {
    type SrcToDestContext: RelayTypes;

    type DstToSrcContext: RelayTypes<
        SrcChain = <Self::SrcToDestContext as RelayTypes>::DstChain,
        DstChain = <Self::SrcToDestContext as RelayTypes>::SrcChain,
        Error = <Self::SrcToDestContext as RelayTypes>::Error,
    >;
}
