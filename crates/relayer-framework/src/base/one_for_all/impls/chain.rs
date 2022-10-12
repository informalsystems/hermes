use async_trait::async_trait;

use crate::base::chain::traits::context::{HasChainTypes, HasIbcChainTypes};
use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::consensus_state::{
    ConsensusStateQuerier, HasConsensusState,
};
use crate::base::chain::traits::queries::received_packet::{
    HasReceivedPacketQuerier, ReceivedPacketQuerier,
};
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::runtime::HasRuntime;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain: OfaBaseChain> HasError for OfaChainWrapper<Chain> {
    type Error = Chain::Error;
}

impl<Chain: OfaBaseChain> HasRuntime for OfaChainWrapper<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }
}

impl<Chain: OfaBaseChain> HasChainTypes for OfaChainWrapper<Chain> {
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
        Chain::encode_raw_message(message, signer)
    }

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_len(message)
    }
}

impl<Chain, Counterparty> HasIbcChainTypes<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
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

impl<Chain, Counterparty> HasIbcEvents<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        Chain::try_extract_write_acknowledgement_event(event)
    }
}

impl<Chain, Counterparty> HasConsensusState<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    type ConsensusState = Chain::ConsensusState;
}

pub struct OfaConsensusStateQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ConsensusStateQuerier<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for OfaConsensusStateQuerier
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_consensus_state(
        chain: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Chain::Error> {
        let consensus_state = chain.chain.query_consensus_state(client_id, height).await?;

        Ok(consensus_state)
    }
}

pub struct OfaReceivedPacketQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ReceivedPacketQuerier<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for OfaReceivedPacketQuerier
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn is_packet_received(
        chain: &OfaChainWrapper<Chain>,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Chain::Error> {
        let is_received = chain
            .chain
            .is_packet_received(port_id, channel_id, sequence)
            .await?;

        Ok(is_received)
    }
}

#[async_trait]
impl<Chain, Counterparty> HasReceivedPacketQuerier<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ReceivedPacketQuerier = OfaReceivedPacketQuerier;
}
