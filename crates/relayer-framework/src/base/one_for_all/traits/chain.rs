//! The `OfaChainWrapper` trait specifies what a chain context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseChain`
//! trait.

use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::chain::traits::queries::consensus_state::ConsensusStateQuerier;
use crate::base::chain::traits::queries::status::ChainStatusQuerier;
use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub trait OfaChainTypes: Async {
    type Preset;

    /**
       Corresponds to
       [`HasErrorType::Error`](crate::base::core::traits::error::HasErrorType::Error).
    */
    type Error: Async + Debug;

    /**
       Corresponds to
       [`HasRuntime::Runtime`](crate::base::runtime::traits::runtime::HasRuntime::Runtime).
    */
    type Runtime: OfaRuntime;

    /**
       Corresponds to
       [`HasChainTypes::Height`](crate::base::chain::traits::types::HasChainTypes::Height).
    */
    type Height: Ord + Async;

    /**
       Corresponds to
       [`HasChainTypes::Timestamp`](crate::base::chain::traits::types::HasChainTypes::Timestamp).
    */
    type Timestamp: Ord + Async;

    /**
       Corresponds to
       [`HasMessageType::Message`](crate::base::chain::traits::types::HasMessageType::Message).
    */
    type Message: Async;

    /**
       Corresponds to
       [`HasEventType::Event`](crate::base::chain::traits::types::HasEventType::Event).
    */
    type Event: Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ClientId`](crate::base::chain::traits::types::HasIbcChainTypes::ClientId).
    */
    type ClientId: Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ConnectionId`](crate::base::chain::traits::types::HasIbcChainTypes::ConnectionId).
    */
    type ConnectionId: Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ChannelId`](crate::base::chain::traits::types::HasIbcChainTypes::ChannelId).
    */
    type ChannelId: Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::PortId`](crate::base::chain::traits::types::HasIbcChainTypes::PortId).
    */
    type PortId: Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::Sequence`](crate::base::chain::traits::types::HasIbcChainTypes::Sequence).
    */
    type Sequence: Async;

    /**
       Corresponds to
       [`HasChainStatus::ChainStatus`](crate::base::chain::traits::queries::status::HasChainStatus::ChainStatus).
    */
    type ChainStatus: Async;

    /**
       Corresponds to
       [`HasConsensusState::ConsensusState`](crate::base::chain::traits::queries::consensus_state::HasConsensusState::ConsensusState).
    */
    type ConsensusState: Async;

    /**
       Corresponds to
       [`HasIbcEvents::WriteAcknowledgementEvent`](crate::base::chain::traits::ibc_event::HasIbcEvents::WriteAcknowledgementEvent).
    */
    type WriteAcknowledgementEvent: Async;
}

#[async_trait]
pub trait OfaBaseChain: OfaChainTypes {
    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error;

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

    async fn query_write_ack_event(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequence: &Counterparty::Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;
}

pub trait OfaChainPreset<Chain>
where
    Chain: OfaBaseChain,
{
    type ChainStatusQuerier: ChainStatusQuerier<OfaChainWrapper<Chain>>;
}

pub trait OfaIbcChainPreset<Chain, Counterparty>: OfaChainPreset<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier: ConsensusStateQuerier<
        OfaChainWrapper<Chain>,
        OfaChainWrapper<Counterparty>,
    >;
}
