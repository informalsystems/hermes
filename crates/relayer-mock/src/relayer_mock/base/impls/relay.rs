use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::packet_relayers::lock::HasPacketLock;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::relay::traits::update_client::UpdateClientMessageBuilder;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use std::vec;

use async_trait::async_trait;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

use crate::relayer_mock::base::error::{BaseError, Error};
use crate::relayer_mock::base::types::aliases::ClientId;
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::components::MockComponents;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;

impl<Name> DelegateComponent<Name> for MockRelayContext {
    type Delegate = MockComponents;
}

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
impl HasPacketLock for MockRelayContext {
    type PacketLock<'a> = ();

    async fn try_acquire_packet_lock<'a>(&'a self, _packet: &'a PacketKey) -> Option<()> {
        Some(())
    }
}
