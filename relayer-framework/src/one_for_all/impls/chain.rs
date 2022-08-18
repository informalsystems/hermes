use async_trait::async_trait;

use crate::one_for_all::impls::message::OfaMessage;
use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::std_prelude::*;
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::error::HasError;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::runtime::HasRuntime;
use crate::traits::queries::consensus_state::{ConsensusStateQuerier, HasConsensusState};
use crate::traits::queries::received_packet::{HasReceivedPacketQuerier, ReceivedPacketQuerier};

impl<Chain: OfaChain> HasError for OfaChainContext<Chain> {
    type Error = OfaErrorContext<Chain::Error>;
}

impl<Chain: OfaChain> HasRuntime for OfaChainContext<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        &self.chain.runtime()
    }
}

impl<Chain: OfaChain> ChainContext for OfaChainContext<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;

    type Message = OfaMessage<Chain>;

    type Event = Chain::Event;
}

impl<Chain, Counterparty> IbcChainContext<OfaChainContext<Counterparty>> for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;

    type IbcMessage = OfaMessage<Chain>;

    type IbcEvent = Chain::Event;
}

impl<Chain, Counterparty> HasIbcEvents<OfaChainContext<Counterparty>> for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: Self::IbcEvent,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        Chain::try_extract_write_acknowledgement_event(event)
    }
}

impl<Chain, Counterparty> HasConsensusState<OfaChainContext<Counterparty>>
    for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    type ConsensusState = Chain::ConsensusState;
}

pub struct OfaConsensusStateQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ConsensusStateQuerier<OfaChainContext<Chain>, OfaChainContext<Counterparty>>
    for OfaConsensusStateQuerier
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_consensus_state(
        chain: &OfaChainContext<Chain>,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, OfaErrorContext<Chain::Error>> {
        let consensus_state = chain.chain.query_consensus_state(client_id, height).await?;

        Ok(consensus_state)
    }
}

pub struct OfaReceivedPacketQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ReceivedPacketQuerier<OfaChainContext<Chain>, OfaChainContext<Counterparty>>
    for OfaReceivedPacketQuerier
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn is_packet_received(
        chain: &OfaChainContext<Chain>,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, OfaErrorContext<Chain::Error>> {
        let is_received = chain
            .chain
            .is_packet_received(port_id, channel_id, sequence)
            .await?;

        Ok(is_received)
    }
}

#[async_trait]
impl<Chain, Counterparty> HasReceivedPacketQuerier<OfaChainContext<Counterparty>>
    for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ReceivedPacketQuerier = OfaReceivedPacketQuerier;
}
