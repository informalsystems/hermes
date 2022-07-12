use ibc::core::ics04_channel::events::WriteAcknowledgement;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::core::ErrorContext;
use ibc_relayer_framework::traits::ibc_event_context::IbcEventContext;
use ibc_relayer_framework::traits::relay_context::RelayContext;
use tendermint::abci::responses::Event;

use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

#[derive(Clone)]
pub struct CosmosChainHandler<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
}

#[derive(Clone)]
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

    type Event = Event;
}

impl<Chain, Counterparty> IbcChainContext<CosmosChainHandler<Counterparty>>
    for CosmosChainHandler<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;

    type IbcEvent = Event;
}

impl<Chain, Counterparty> IbcEventContext<CosmosChainHandler<Counterparty>>
    for CosmosChainHandler<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type WriteAcknowledgementEvent = WriteAcknowledgement;
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

    fn source_chain(&self) -> &Self::SrcChain {
        &self.src_handle
    }

    fn destination_chain(&self) -> &Self::DstChain {
        &self.dst_handle
    }

    fn source_client_id(&self) -> &ClientId {
        &self.dst_to_src_client.id
    }

    fn destination_client_id(&self) -> &ClientId {
        &self.src_to_dst_client.id
    }
}
