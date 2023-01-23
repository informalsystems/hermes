//! The `OfaChainWrapper` trait specifies what a chain context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseChain`
//! trait.

use alloc::sync::Arc;
use async_trait::async_trait;
use core::fmt::Debug;

use crate::base::chain::traits::queries::consensus_state::ConsensusStateQuerier;
use crate::base::chain::traits::queries::status::ChainStatusQuerier;
use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::subscription::Subscription;
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
    type Runtime: OfaBaseRuntime;

    /**
       Corresponds to
       [`HasChainTypes::Height`](crate::base::chain::traits::types::height::HasHeightType::Height).
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

    type ChainId: Eq + Async;

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
       [`HasWriteAcknowledgementEvent::WriteAcknowledgementEvent`](crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent::WriteAcknowledgementEvent).
    */
    type WriteAcknowledgementEvent: Async;

    type SendPacketEvent: Async;
}

#[async_trait]
pub trait OfaBaseChain: OfaChainTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaBaseRuntime>::Error) -> Self::Error;

    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error>;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;

    fn chain_id(&self) -> &Self::ChainId;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaBaseChain
where
    Counterparty: OfaIbcChain<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    type IncomingPacket: Async;

    type OutgoingPacket: Async;

    fn incoming_packet_src_channel_id(packet: &Self::IncomingPacket) -> &Counterparty::ChannelId;

    fn incoming_packet_dst_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId;

    fn incoming_packet_src_port(packet: &Self::IncomingPacket) -> &Counterparty::PortId;

    fn incoming_packet_dst_port(packet: &Self::IncomingPacket) -> &Self::PortId;

    fn incoming_packet_sequence(packet: &Self::IncomingPacket) -> &Counterparty::Sequence;

    fn incoming_packet_timeout_height(packet: &Self::IncomingPacket) -> Option<&Self::Height>;

    fn incoming_packet_timeout_timestamp(packet: &Self::IncomingPacket) -> &Self::Timestamp;

    fn outgoing_packet_src_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId;

    fn outgoing_packet_dst_channel_id(packet: &Self::OutgoingPacket) -> &Counterparty::ChannelId;

    fn outgoing_packet_src_port(packet: &Self::OutgoingPacket) -> &Self::PortId;

    fn outgoing_packet_dst_port(packet: &Self::OutgoingPacket) -> &Counterparty::PortId;

    fn outgoing_packet_sequence(packet: &Self::OutgoingPacket) -> &Self::Sequence;

    fn outgoing_packet_timeout_height(
        packet: &Self::OutgoingPacket,
    ) -> Option<&Counterparty::Height>;

    fn outgoing_packet_timeout_timestamp(packet: &Self::OutgoingPacket)
        -> &Counterparty::Timestamp;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent>;

    fn extract_packet_from_send_packet_event(event: &Self::SendPacketEvent)
        -> Self::OutgoingPacket;

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket;

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Counterparty::ChainId, Self::Error>;

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

    async fn build_receive_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Counterparty::Message, Self::Error>;

    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;
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
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type ConsensusStateQuerier: ConsensusStateQuerier<
        OfaChainWrapper<Chain>,
        OfaChainWrapper<Counterparty>,
    >;
}
