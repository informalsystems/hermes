use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::ibc_message_sender::{
    CanSendIbcMessages, IbcMessageSender, MainSink,
};
use ibc_relayer_components::relay::traits::messages::update_client::{
    CanBuildUpdateClientMessage, UpdateClientMessageBuilder,
};
use ibc_relayer_components::relay::traits::packet_relayer::{CanRelayPacket, PacketRelayer};
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::{
    AckPacketRelayer, CanRelayAckPacket,
};
use ibc_relayer_components::relay::traits::packet_relayers::lock::HasPacketLock;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::{
    CanRelayReceivePacket, ReceivePacketRelayer,
};
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::{
    CanRelayTimeoutUnorderedPacket, TimeoutUnorderedPacketRelayer,
};
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use std::vec;

use async_trait::async_trait;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

use crate::relayer_mock::base::error::{BaseError, Error};
use crate::relayer_mock::base::types::aliases::ClientId;
use crate::relayer_mock::base::types::events::{Event, WriteAcknowledgementEvent};
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::components;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;

impl HasErrorType for MockRelayContext {
    type Error = Error;
}

impl HasRuntime for MockRelayContext {
    type Runtime = MockRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }
}

impl HasLoggerType for MockRelayContext {
    type Logger = TracingLogger;
}

impl HasLogger for MockRelayContext {
    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }
}

impl HasRelayChains for MockRelayContext {
    type SrcChain = MockChainContext;

    type DstChain = MockChainContext;

    fn src_chain_error(e: Error) -> Self::Error {
        e
    }

    fn dst_chain_error(e: Error) -> Self::Error {
        e
    }

    fn src_chain(&self) -> &MockChainContext {
        &self.src_chain
    }

    fn dst_chain(&self) -> &MockChainContext {
        &self.dst_chain
    }

    fn src_client_id(&self) -> &ClientId {
        self.dst_to_src_client()
    }

    fn dst_client_id(&self) -> &ClientId {
        self.src_to_dst_client()
    }
}

pub struct MockBuildUpdateClientMessage;

#[async_trait]
impl UpdateClientMessageBuilder<MockRelayContext, SourceTarget> for MockBuildUpdateClientMessage {
    async fn build_update_client_messages(
        context: &MockRelayContext,
        _target: SourceTarget,
        height: &MockHeight,
    ) -> Result<Vec<MockMessage>, Error> {
        let state = context.dst_chain.query_state_at_height(*height)?;
        Ok(vec![MockMessage::UpdateClient(
            context.src_client_id().to_string(),
            *height,
            state,
        )])
    }
}

#[async_trait]
impl UpdateClientMessageBuilder<MockRelayContext, DestinationTarget>
    for MockBuildUpdateClientMessage
{
    async fn build_update_client_messages(
        context: &MockRelayContext,
        _target: DestinationTarget,
        height: &MockHeight,
    ) -> Result<Vec<MockMessage>, Error> {
        let state = context.src_chain.query_state_at_height(*height)?;
        Ok(vec![MockMessage::UpdateClient(
            context.dst_client_id().to_string(),
            *height,
            state,
        )])
    }
}

#[async_trait]
impl CanBuildUpdateClientMessage<SourceTarget> for MockRelayContext {
    async fn build_update_client_messages(
        &self,
        target: SourceTarget,
        height: &MockHeight,
    ) -> Result<Vec<MockMessage>, Error> {
        components::UpdateClientMessageBuilder::build_update_client_messages(self, target, height)
            .await
    }
}

#[async_trait]
impl CanBuildUpdateClientMessage<DestinationTarget> for MockRelayContext {
    async fn build_update_client_messages(
        &self,
        target: DestinationTarget,
        height: &MockHeight,
    ) -> Result<Vec<MockMessage>, Error> {
        components::UpdateClientMessageBuilder::build_update_client_messages(self, target, height)
            .await
    }
}

#[async_trait]
impl HasPacketLock for MockRelayContext {
    type PacketLock<'a> = ();

    async fn try_acquire_packet_lock<'a>(&'a self, _packet: &'a PacketKey) -> Option<()> {
        Some(())
    }
}

#[async_trait]
impl CanSendIbcMessages<MainSink, SourceTarget> for MockRelayContext {
    async fn send_messages(
        &self,
        _target: SourceTarget,
        messages: Vec<MockMessage>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        <components::IbcMessageSender as IbcMessageSender<
            MockRelayContext,
            MainSink,
            SourceTarget,
        >>::send_messages(self, messages)
        .await
    }
}

#[async_trait]
impl CanSendIbcMessages<MainSink, DestinationTarget> for MockRelayContext {
    async fn send_messages(
        &self,
        _target: DestinationTarget,
        messages: Vec<MockMessage>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        <components::IbcMessageSender as IbcMessageSender<
            MockRelayContext,
            MainSink,
            DestinationTarget,
        >>::send_messages(self, messages)
        .await
    }
}

#[async_trait]
impl CanRelayAckPacket for MockRelayContext {
    async fn relay_ack_packet(
        &self,
        destination_height: &MockHeight,
        packet: &PacketKey,
        ack: &WriteAcknowledgementEvent,
    ) -> Result<(), Error> {
        components::AckPacketRelayer::relay_ack_packet(self, destination_height, packet, ack).await
    }
}

#[async_trait]
impl CanRelayReceivePacket for MockRelayContext {
    async fn relay_receive_packet(
        &self,
        source_height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<Option<WriteAcknowledgementEvent>, Error> {
        components::ReceivePacketRelayer::relay_receive_packet(self, source_height, packet).await
    }
}

#[async_trait]
impl CanRelayTimeoutUnorderedPacket for MockRelayContext {
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<(), Self::Error> {
        components::TimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
            self,
            destination_height,
            packet,
        )
        .await
    }
}

#[async_trait]
impl CanRelayPacket for MockRelayContext {
    async fn relay_packet(&self, packet: &PacketKey) -> Result<(), Error> {
        components::PacketRelayer::relay_packet(self, packet).await
    }
}
