use async_trait::async_trait;

use crate::one_for_all::traits::components::chain::OfaChainComponents;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::std_prelude::*;
use crate::traits::core::Async;

#[async_trait]
pub trait OfaChain: Async + Clone {
    type Components: OfaChainComponents<Self>;

    type Error: OfaError;

    type Runtime: OfaRuntime<Error = Self::Error>;

    type Height: Ord + Async;

    type Timestamp: Async;

    type Message: Async;

    type RawMessage: Async;

    type Signer: Async;

    type Event: Async;

    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    type ChainStatus: Async;

    type WriteAcknowledgementEvent: Async + TryFrom<Self::Event, Error = Self::Error>;

    type CounterpartySequence: Async;

    type CounterpartyHeight: Async;

    type ConsensusState: Async;

    type CounterpartyConsensusState: Async;

    fn encode_raw_message(
        message: &Self::Message,
        signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error>;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;

    fn source_message_height(message: &Self::Message) -> Option<Self::CounterpartyHeight>;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;

    fn runtime(&self) -> &Self::Runtime;

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::CounterpartyHeight,
    ) -> Result<Self::CounterpartyConsensusState, Self::Error>;

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::CounterpartySequence,
    ) -> Result<bool, Self::Error>;
}
