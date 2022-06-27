use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::foreign_client::ForeignClient;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::Async;
use crate::traits::core::ErrorContext;
use crate::traits::relay_context::RelayContext;

pub struct CosmosChainHandler<Handle> {
    pub handle: Handle,
}

pub struct CosmosRelayHandler<SrcChain, DstChain> {
    pub src_handle: CosmosChainHandler<SrcChain>,
    pub dst_handle: CosmosChainHandler<DstChain>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
}

impl<Handle: Async> ErrorContext for CosmosChainHandler<Handle> {
    type Error = Error;
}

impl<Handle: Async> ChainContext for CosmosChainHandler<Handle> {
    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = IbcEvent;
}

impl<Chain, Counterparty> IbcChainContext<CosmosChainHandler<Counterparty>>
    for CosmosChainHandler<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;

    type IbcEvent = IbcEvent;
}

impl<SrcChain, DstChain> ErrorContext for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type Error = Error;
}

impl<SrcChain, DstChain> RelayContext for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: Async,
    DstChain: Async,
{
    type SrcChain = CosmosChainHandler<SrcChain>;

    type DstChain = CosmosChainHandler<DstChain>;

    type Packet = Packet;

    fn source_context(&self) -> &Self::SrcChain {
        &self.src_handle
    }

    fn destination_context(&self) -> &Self::DstChain {
        &self.dst_handle
    }
}
