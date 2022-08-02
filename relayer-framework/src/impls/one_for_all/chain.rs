use async_trait::async_trait;

use crate::impls::one_for_all::error::OfaErrorContext;
use crate::impls::one_for_all::message::OfaMessage;
use crate::impls::one_for_all::runtime::OfaRuntimeContext;
use crate::std_prelude::*;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::ErrorContext;
use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::one_for_all::chain::OfaChain;
use crate::traits::queries::consensus_state::{ConsensusStateContext, ConsensusStateQuerier};
use crate::traits::queries::received_packet::ReceivedPacketQuerier;
use crate::traits::runtime::context::RuntimeContext;

pub struct OfaChainContext<Chain: OfaChain> {
    pub chain: Chain,
    pub runtime: OfaRuntimeContext<Chain::Runtime>,
}

impl<Chain: OfaChain> ErrorContext for OfaChainContext<Chain> {
    type Error = OfaErrorContext<Chain::Error>;
}

impl<Chain: OfaChain> RuntimeContext for OfaChainContext<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }
}

impl<Chain: OfaChain> ChainContext for OfaChainContext<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;

    type Message = OfaMessage<Chain>;

    type Event = Chain::Event;
}

impl<Chain, Counterparty> IbcChainContext<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;

    type IbcMessage = OfaMessage<Chain>;

    type IbcEvent = Chain::Event;
}

impl<Chain, Counterparty> IbcEventContext<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;
}

impl<Chain, Counterparty> ConsensusStateContext<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type ConsensusState = Chain::ConsensusState;
}

#[async_trait]
impl<Chain, Counterparty> ConsensusStateQuerier<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
    Counterparty: ConsensusStateContext<Self, ConsensusState = Chain::CounterpartyConsensusState>,
{
    async fn query_consensus_state(
        &self,
        client_id: &Chain::ClientId,
        height: &Chain::CounterpartyHeight,
    ) -> Result<Chain::CounterpartyConsensusState, Self::Error> {
        let consensus_state = self.chain.query_consensus_state(client_id, height).await?;

        Ok(consensus_state)
    }
}

#[async_trait]
impl<Chain, Counterparty> ReceivedPacketQuerier<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: IbcChainContext<
        Self,
        Height = Chain::CounterpartyHeight,
        Sequence = Chain::CounterpartySequence,
    >,
{
    async fn is_packet_received(
        &self,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error> {
        let is_received = self
            .chain
            .is_packet_received(port_id, channel_id, sequence)
            .await?;

        Ok(is_received)
    }
}
