//! The `OfaChainWrapper` trait specifies what a chain context needs to provide
//! in order to gain access to the APIs provided by the [`AfoBaseChain`]
//! trait.

use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::std_prelude::*;

pub trait OfaBaseChainTypes: Async {
    type Components;

    type Error: Async + Debug;

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
}

#[async_trait]
pub trait OfaBaseChain: OfaBaseChainTypes {
    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime>;

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

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaBaseChain
where
    Counterparty: OfaBaseChainTypes,
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
