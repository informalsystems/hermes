//! The `OfaChainContext` trait specifies what a chain context needs to provide
//! in order to gain access to the APIs provided by the [`AfoChainContext`]
//! trait.

use async_trait::async_trait;

use crate::addons::batch::context::BatchChannel;
use crate::core::traits::core::Async;
use crate::one_for_all::traits::batch::OfaBatch;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::one_for_all::traits::telemetry::{OfaTelemetry, OfaTelemetryWrapper};
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

pub trait OfaChainTypes: Async {
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
}

#[async_trait]
pub trait OfaChain: OfaChainTypes {
    type Components;

    type Telemetry: OfaTelemetry;

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

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaChain
where
    Counterparty: OfaChainTypes,
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

pub trait OfaFullChain: OfaChainTypes {
    type BatchContext: OfaBatch<Self>;

    fn batch_channel(
        &self,
    ) -> &BatchChannel<
        <Self::BatchContext as OfaBatch<Self>>::BatchSender,
        <Self::BatchContext as OfaBatch<Self>>::BatchReceiver,
    >;
}
