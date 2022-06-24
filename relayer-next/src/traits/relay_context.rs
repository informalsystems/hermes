use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::CoreTraits;
use crate::traits::packet::IbcPacket;

pub trait RelayContext: CoreTraits {
    type Error: CoreTraits;

    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + CoreTraits;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;
}

pub trait RelayContextPair: CoreTraits {
    type SrcContext: RelayContext;

    type DstContext: RelayContext<
        SrcChain = <Self::SrcContext as RelayContext>::DstChain,
        DstChain = <Self::SrcContext as RelayContext>::SrcChain,
        Error = <Self::SrcContext as RelayContext>::Error,
    >;

    fn source_context(&self) -> &Self::SrcContext;

    fn destination_context(&self) -> &Self::DstContext;
}
