use crate::traits::chain_types::{IbcChainContext, IbcChainTypes};
use crate::traits::core::CoreTraits;
use crate::traits::message::{IbcMessage, Message};
use crate::traits::packet::IbcPacket;

pub trait RelayTypes: CoreTraits {
    type Error: CoreTraits;

    type SrcHeight: CoreTraits;

    type DstHeight: CoreTraits;

    type SrcTimestamp: CoreTraits;

    type DstTimestamp: CoreTraits;

    type SrcMessage: CoreTraits + Message + IbcMessage<Self::DstChain>;

    type DstMessage: CoreTraits + Message + IbcMessage<Self::SrcChain>;

    type SrcChannelId: CoreTraits;

    type DstChannelId: CoreTraits;

    type SrcPortId: CoreTraits;

    type DstPortId: CoreTraits;

    type SrcSequence: CoreTraits;

    type DstSequence: CoreTraits;

    type SrcIbcEvent: CoreTraits;

    type DstIbcEvent: CoreTraits;

    type SrcChain: IbcChainTypes<
        Self::DstChain,
        Error = Self::Error,
        Height = Self::SrcHeight,
        Timestamp = Self::SrcTimestamp,
        Message = Self::SrcMessage,
        ChannelId = Self::SrcChannelId,
        PortId = Self::SrcPortId,
        Sequence = Self::SrcSequence,
        IbcEvent = Self::SrcIbcEvent,
    >;

    type DstChain: IbcChainTypes<
        Self::SrcChain,
        Error = Self::Error,
        Height = Self::DstHeight,
        Timestamp = Self::DstTimestamp,
        Message = Self::DstMessage,
        ChannelId = Self::DstChannelId,
        PortId = Self::DstPortId,
        Sequence = Self::DstSequence,
        IbcEvent = Self::DstIbcEvent,
    >;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + CoreTraits;
}

pub trait RelayContext: CoreTraits {
    type Error: CoreTraits;

    type SrcChainTypes: IbcChainTypes<Self::DstChainTypes, Error = Self::Error>;

    type DstChainTypes: IbcChainTypes<Self::SrcChainTypes, Error = Self::Error>;

    type RelayTypes: RelayTypes<
        Error = Self::Error,
        SrcChain = Self::SrcChainTypes,
        DstChain = Self::DstChainTypes,
    >;

    type SrcChainContext: IbcChainContext<
        Self::DstChainTypes,
        IbcChainTypes = Self::SrcChainTypes,
        Error = Self::Error,
    >;

    type DstChainContext: IbcChainContext<
        Self::SrcChainTypes,
        IbcChainTypes = Self::DstChainTypes,
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
