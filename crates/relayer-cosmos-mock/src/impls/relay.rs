use alloc::boxed::Box;
use alloc::vec::Vec;
use async_trait::async_trait;

use ibc::clients::ics07_tendermint::client_type;
use ibc::clients::ics07_tendermint::header::Header;
use ibc::core::ics02_client::msgs::update_client::MsgUpdateClient;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::{Msg, ValidationContext};
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
use crate::util::dummy::dummy_signer;
use crate::util::mutex::MutexUtil;

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
        context: &MockCosmosRelay,
        _target: SourceTarget,
        height: &Height,
    ) -> Result<Vec<Any>, Error> {
        let client_counter = context.dst_chain().ibc_context().client_counter()?;

        let client_id = ClientId::new(client_type(), client_counter)?;

        let client_state = context
            .dst_chain()
            .ibc_context()
            .client_state(&ClientId::default())?;

        let revision_height = height.revision_height() as usize;

        let blocks = context.src_chain().blocks.acquire_mutex();

        if revision_height > blocks.len() {
            return Err(Error::invalid("block index out of bounds"));
        }
        let light_block = blocks[revision_height - 1].clone();

        let header = Header {
            signed_header: light_block.signed_header,
            validator_set: light_block.validators,
            trusted_height: client_state.latest_height,
            trusted_next_validator_set: light_block.next_validators,
        };

        let msg_update_client = MsgUpdateClient {
            client_id,
            client_message: header.into(),
            signer: dummy_signer(),
        };

        Ok(vec![msg_update_client.to_any()])
    }
}

#[async_trait]
impl UpdateClientMessageBuilder<MockCosmosRelay, DestinationTarget>
    for MockCosmosBuildUpdateClientMessage
{
    async fn build_update_client_messages(
        context: &MockCosmosRelay,
        _target: DestinationTarget,
        height: &Height,
    ) -> Result<Vec<Any>, Error> {
        let client_counter = context.src_chain().ibc_context().client_counter()?;

        let client_id = ClientId::new(client_type(), client_counter)?;

        let client_state = context
            .src_chain()
            .ibc_context()
            .client_state(&ClientId::default())?;

        let revision_height = height.revision_height() as usize;

        let blocks = context.dst_chain().blocks.acquire_mutex();

        if revision_height > blocks.len() {
            return Err(Error::invalid("block index out of bounds"));
        }

        let light_block = blocks[revision_height - 1].clone();

        let header = Header {
            signed_header: light_block.signed_header,
            validator_set: light_block.validators,
            trusted_height: client_state.latest_height,
            trusted_next_validator_set: light_block.next_validators,
        };

        let msg_update_client = MsgUpdateClient {
            client_id,
            client_message: header.into(),
            signer: dummy_signer(),
        };

        Ok(vec![msg_update_client.to_any()])
    }
}

#[async_trait]
impl HasPacketLock for MockCosmosRelay {
    type PacketLock<'a> = ();

    async fn try_acquire_packet_lock<'a>(&'a self, _packet: &'a Packet) -> Option<()> {
        Some(())
    }
}
