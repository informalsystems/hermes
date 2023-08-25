use alloc::boxed::Box;
use alloc::vec::Vec;
use async_trait::async_trait;

use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::{Any, Height};

use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::HasLogger;
use ibc_relayer_components::logger::traits::has_logger::HasLoggerType;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::packet_relayers::lock::HasPacketLock;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::relay::traits::update_client::UpdateClientMessageBuilder;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;

use crate::contexts::chain::MockCosmosChain;
use crate::contexts::relay::MockCosmosRelay;
use crate::contexts::runtime::MockRuntimeContext;
use crate::impls::components::MockCosmosComponents;
use crate::types::error::Error;

impl<Name> DelegateComponent<Name> for MockCosmosRelay {
    type Delegate = MockCosmosComponents;
}

impl HasErrorType for MockCosmosRelay {
    type Error = Error;
}

impl HasRuntime for MockCosmosRelay {
    type Runtime = MockRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        Error::source(e)
    }
}

impl HasLoggerType for MockCosmosRelay {
    type Logger = TracingLogger;
}

impl HasLogger for MockCosmosRelay {
    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }
}

impl HasRelayChains for MockCosmosRelay {
    type SrcChain = MockCosmosChain;

    type DstChain = MockCosmosChain;

    fn src_chain_error(e: Error) -> Self::Error {
        e
    }

    fn dst_chain_error(e: Error) -> Self::Error {
        e
    }

    fn src_chain(&self) -> &MockCosmosChain {
        &self.src_chain
    }

    fn dst_chain(&self) -> &MockCosmosChain {
        &self.dst_chain
    }

    fn src_client_id(&self) -> &ClientId {
        self.src_client_id()
    }

    fn dst_client_id(&self) -> &ClientId {
        self.dst_client_id()
    }
}

pub struct MockCosmosBuildUpdateClientMessage;

#[async_trait]
impl UpdateClientMessageBuilder<MockCosmosRelay, SourceTarget>
    for MockCosmosBuildUpdateClientMessage
{
    async fn build_update_client_messages(
        _context: &MockCosmosRelay,
        _target: SourceTarget,
        _height: &Height,
    ) -> Result<Vec<Any>, Error> {
        Ok(vec![])
    }
}

#[async_trait]
impl UpdateClientMessageBuilder<MockCosmosRelay, DestinationTarget>
    for MockCosmosBuildUpdateClientMessage
{
    async fn build_update_client_messages(
        _context: &MockCosmosRelay,
        _target: DestinationTarget,
        _height: &Height,
    ) -> Result<Vec<Any>, Error> {
        Ok(vec![])
    }
}

#[async_trait]
impl HasPacketLock for MockCosmosRelay {
    type PacketLock<'a> = ();

    async fn try_acquire_packet_lock<'a>(&'a self, _packet: &'a Packet) -> Option<()> {
        Some(())
    }
}
