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

use crate::contexts::chain::MockCosmosContext;
use crate::contexts::relay::MockCosmosRelay;
use crate::contexts::runtime::MockRuntimeContext;
use crate::impls::components::MockCosmosComponents;
use crate::traits::endpoint::Endpoint;
use crate::traits::handle::BasecoinHandle;
use crate::types::error::Error;
use crate::util::dummy::dummy_signer;

impl<Name, SrcChain, DstChain> DelegateComponent<Name> for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type Delegate = MockCosmosComponents;
}

impl<SrcChain, DstChain> HasErrorType for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type Error = Error;
}

impl<SrcChain, DstChain> HasRuntime for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type Runtime = MockRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        Error::source(e)
    }
}

impl<SrcChain, DstChain> HasLoggerType for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type Logger = TracingLogger;
}

impl<SrcChain, DstChain> HasLogger for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }
}

impl<SrcChain, DstChain> HasRelayChains for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type SrcChain = MockCosmosContext<SrcChain>;

    type DstChain = MockCosmosContext<DstChain>;

    fn src_chain_error(e: Error) -> Self::Error {
        e
    }

    fn dst_chain_error(e: Error) -> Self::Error {
        e
    }

    fn src_chain(&self) -> &MockCosmosContext<SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &MockCosmosContext<DstChain> {
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
impl<SrcChain, DstChain>
    UpdateClientMessageBuilder<MockCosmosRelay<SrcChain, DstChain>, SourceTarget>
    for MockCosmosBuildUpdateClientMessage
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    async fn build_update_client_messages(
        context: &MockCosmosRelay<SrcChain, DstChain>,
        _target: SourceTarget,
        height: &Height,
    ) -> Result<Vec<Any>, Error> {
        let client_counter = context.dst_chain().ibc_context().client_counter()?;

        let client_id = ClientId::new(client_type(), client_counter)?;

        let client_state = context
            .dst_chain()
            .ibc_context()
            .client_state(&ClientId::default())?;

        let light_block = context.src_chain().query_light_block(height)?;

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
impl<SrcChain, DstChain>
    UpdateClientMessageBuilder<MockCosmosRelay<SrcChain, DstChain>, DestinationTarget>
    for MockCosmosBuildUpdateClientMessage
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    async fn build_update_client_messages(
        context: &MockCosmosRelay<SrcChain, DstChain>,
        _target: DestinationTarget,
        height: &Height,
    ) -> Result<Vec<Any>, Error> {
        let client_counter = context.src_chain().ibc_context().client_counter()?;

        let client_id = ClientId::new(client_type(), client_counter)?;

        let client_state = context
            .src_chain()
            .ibc_context()
            .client_state(&ClientId::default())?;

        let light_block = context.dst_chain().query_light_block(height)?;

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
impl<SrcChain, DstChain> HasPacketLock for MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    type PacketLock<'a> = ();

    async fn try_acquire_packet_lock<'a>(&'a self, _packet: &'a Packet) -> Option<()> {
        Some(())
    }
}
