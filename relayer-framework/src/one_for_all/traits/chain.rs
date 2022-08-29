//! The [`OfaChainContext`] (where "Ofa" stands for "one for all") 
//! trait can be implemented by a chain in lieu of the [`ChainContext`]
//! trait in the common case where the implementing chain wants
//! sensible defaults. 

use async_trait::async_trait;

use crate::core::traits::core::Async;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaChainContext<Chain> {
    pub chain: Chain,
}

impl<Chain> OfaChainContext<Chain> {
    pub fn new(chain: Chain) -> Self {
        Self { chain }
    }
}

#[async_trait]
pub trait OfaChain: Async {
    type Components;

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

    type ConsensusState: Async;

    type WriteAcknowledgementEvent: Async;

    fn encode_raw_message(
        message: &Self::Message,
        signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error>;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;

    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime>;

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaChain
where
    Counterparty: OfaChain,
{
    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error>;
}
