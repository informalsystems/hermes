use async_trait::async_trait;

use crate::core::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::core::traits::contexts::error::HasError;
use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::runtime::HasRuntime;
use crate::core::traits::contexts::telemetry::HasTelemetry;
use crate::core::traits::queries::consensus_state::{ConsensusStateQuerier, HasConsensusState};
use crate::core::traits::queries::received_packet::{
    HasReceivedPacketQuerier, ReceivedPacketQuerier,
};
use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::std_prelude::*;

impl<Chain: OfaChain> HasError for OfaChainContext<Chain> {
    type Error = OfaErrorContext<Chain::Error>;
}

impl<Chain: OfaChain> HasRuntime for OfaChainContext<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }
}

impl<Chain: OfaChain> HasTelemetry for OfaChainContext<Chain> {
    type Telemetry = Chain::Telemetry;

    fn telemetry(&self) -> &Self::Telemetry {
        self.chain.telemetry()
    }
}

impl<Chain: OfaChain> ChainContext for OfaChainContext<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;

    type Message = Chain::Message;

    type RawMessage = Chain::RawMessage;

    type Signer = Chain::Signer;

    type Event = Chain::Event;

    fn encode_message(
        message: &Self::Message,
        signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error> {
        Chain::encode_raw_message(message, signer).map_err(OfaErrorContext::new)
    }

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_len(message).map_err(OfaErrorContext::new)
    }
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

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height> {
        Chain::counterparty_message_height(message)
    }
}

impl<Chain, Counterparty> HasIbcEvents<OfaChainContext<Counterparty>> for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChain,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
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
