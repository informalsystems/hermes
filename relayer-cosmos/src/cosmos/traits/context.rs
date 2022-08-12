use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer_framework::traits::contexts::chain::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::contexts::relay::RelayContext;

use crate::cosmos::message::CosmosIbcMessage;

pub trait CosmosChainContext:
    ChainContext<Height = Height, Timestamp = Timestamp, Message = CosmosIbcMessage, Event = IbcEvent>
{
}

impl<Context> CosmosChainContext for Context where
    Context: ChainContext<
        Height = Height,
        Timestamp = Timestamp,
        Message = CosmosIbcMessage,
        Event = IbcEvent,
    >
{
}

pub trait CosmosIbcChainContext<Counterparty>:
    CosmosChainContext
    + IbcChainContext<
        Counterparty,
        ClientId = ClientId,
        ConnectionId = ConnectionId,
        ChannelId = ChannelId,
        PortId = PortId,
        Sequence = Sequence,
        IbcMessage = CosmosIbcMessage,
        IbcEvent = IbcEvent,
    >
where
    Counterparty: ChainContext,
{
}

impl<Context, Counterparty> CosmosIbcChainContext<Counterparty> for Context
where
    Context: CosmosChainContext,
    Context: IbcChainContext<
        Counterparty,
        ClientId = ClientId,
        ConnectionId = ConnectionId,
        ChannelId = ChannelId,
        PortId = PortId,
        Sequence = Sequence,
        IbcMessage = CosmosIbcMessage,
        IbcEvent = IbcEvent,
    >,
    Counterparty: ChainContext,
{
}

pub trait CosmosRelayContext: RelayContext<Packet = Packet> {
    type CosmosSrcChain: CosmosIbcChainContext<Self::CosmosDstChain>;
    type CosmosDstChain: CosmosIbcChainContext<Self::CosmosSrcChain>;
}

impl<Context> CosmosRelayContext for Context
where
    Context: RelayContext<Packet = Packet>,
    Context::SrcChain: CosmosIbcChainContext<Context::DstChain>,
    Context::DstChain: CosmosIbcChainContext<Context::SrcChain>,
{
    type CosmosSrcChain = Context::SrcChain;
    type CosmosDstChain = Context::DstChain;
}
