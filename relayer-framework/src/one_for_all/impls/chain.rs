use async_trait::async_trait;

use crate::one_for_all::impls::error::OfaHasError;
use crate::one_for_all::impls::message::OfaMessage;
use crate::one_for_all::impls::runtime::OfaHasRuntime;
use crate::one_for_all::traits::chain::OfaChain;
use crate::std_prelude::*;
use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::error::HasError;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::runtime::HasRuntime;
use crate::traits::queries::consensus_state::{
    CanQueryConsensusState, ConsensusStateQuerier, HasConsensusState,
};
use crate::traits::queries::received_packet::ReceivedPacketQuerier;

pub struct OfaChainContext<Chain: OfaChain> {
    pub chain: Chain,
    pub runtime: OfaHasRuntime<Chain::Runtime>,
}

impl<Chain: OfaChain> OfaChainContext<Chain> {
    pub fn new(chain: Chain, runtime: Chain::Runtime) -> Self {
        Self {
            chain,
            runtime: OfaHasRuntime::new(runtime),
        }
    }
}

impl<Chain: OfaChain> HasError for OfaChainContext<Chain> {
    type Error = OfaHasError<Chain::Error>;
}

impl<Chain: OfaChain> HasRuntime for OfaChainContext<Chain> {
    type Runtime = OfaHasRuntime<Chain::Runtime>;

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

impl<Chain, Counterparty> HasIbcEvents<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;
}

impl<Chain, Counterparty> HasConsensusState<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type ConsensusState = Chain::ConsensusState;
}

pub struct OfaConsensusStateQuerier;

#[async_trait]
impl<Chain, Counterparty> ConsensusStateQuerier<OfaChainContext<Chain>, Counterparty>
    for OfaConsensusStateQuerier
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
    Counterparty: HasConsensusState<
        OfaChainContext<Chain>,
        ConsensusState = Chain::CounterpartyConsensusState,
    >,
{
    async fn query_consensus_state(
        chain: &OfaChainContext<Chain>,
        client_id: &Chain::ClientId,
        height: &Chain::CounterpartyHeight,
    ) -> Result<Chain::CounterpartyConsensusState, OfaHasError<Chain::Error>> {
        let consensus_state = chain.chain.query_consensus_state(client_id, height).await?;

        Ok(consensus_state)
    }
}

impl<Chain, Counterparty> CanQueryConsensusState<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
    Counterparty: HasConsensusState<
        OfaChainContext<Chain>,
        ConsensusState = Chain::CounterpartyConsensusState,
    >,
{
    type ConsensusStateQuerier = OfaConsensusStateQuerier;
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
