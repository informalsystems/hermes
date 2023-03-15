use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayTypes};
use ibc_relayer_all_in_one::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_types::core::ics04_channel::packet::{Packet, Sequence};
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, PortId};
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::base::error::{BaseError, Error};
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::message::CosmosIbcMessage;
use crate::base::types::relay::CosmosRelayWrapper;

impl<Relay> OfaRelayTypes for CosmosRelayWrapper<Relay>
where
    Relay: CosmosRelay,
{
    type Preset = Relay::Preset;

    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type Packet = Packet;

    type SrcChain = CosmosChainWrapper<Relay::SrcChain>;

    type DstChain = CosmosChainWrapper<Relay::DstChain>;
}

#[async_trait]
impl<Relay> OfaBaseRelay for CosmosRelayWrapper<Relay>
where
    Relay: CosmosRelay,
{
    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn src_chain_error(e: Error) -> Error {
        e
    }

    fn dst_chain_error(e: Error) -> Error {
        e
    }

    fn packet_src_port(packet: &Packet) -> &PortId {
        &packet.source_port
    }

    fn packet_src_channel_id(packet: &Packet) -> &ChannelId {
        &packet.source_channel
    }

    fn packet_dst_port(packet: &Packet) -> &PortId {
        &packet.destination_port
    }

    fn packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        &packet.destination_channel
    }

    fn packet_sequence(packet: &Packet) -> &Sequence {
        &packet.sequence
    }

    fn packet_timeout_height(packet: &Packet) -> Option<&Height> {
        match &packet.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        &packet.timeout_timestamp
    }

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        self.relay.runtime()
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    fn src_client_id(&self) -> &ClientId {
        &self.relay.dst_to_src_client().id
    }

    fn dst_client_id(&self) -> &ClientId {
        &self.relay.src_to_dst_client().id
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        self.relay.src_chain()
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        self.relay.dst_chain()
    }

    async fn build_src_update_client_messages(
        &self,
        height: &Height,
    ) -> Result<Vec<CosmosIbcMessage>, Self::Error> {
        let height = *height;
        let client = self.relay.dst_to_src_client().clone();

        self.runtime()
            .runtime
            .runtime
            .spawn_blocking(move || build_update_client_messages(&client, height))
            .await
            .map_err(BaseError::join)?
    }

    async fn build_dst_update_client_messages(
        &self,
        height: &Height,
    ) -> Result<Vec<CosmosIbcMessage>, Self::Error> {
        let height = *height;
        let client = self.relay.src_to_dst_client().clone();

        self.runtime()
            .runtime
            .runtime
            .spawn_blocking(move || build_update_client_messages(&client, height))
            .await
            .map_err(BaseError::join)?
    }
}

fn build_update_client_messages<DstChain, SrcChain>(
    foreign_client: &ForeignClient<DstChain, SrcChain>,
    height: Height,
) -> Result<Vec<CosmosIbcMessage>, Error>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let messages = foreign_client
        .build_update_client_with_trusted(height, None)
        .map_err(BaseError::foreign_client)?;

    let ibc_messages = messages
        .into_iter()
        .map(|update_message| {
            CosmosIbcMessage::new(Some(height), move |signer| {
                let mut update_message = update_message.clone();
                update_message.signer = signer.clone();
                Ok(update_message.to_any())
            })
        })
        .collect();

    Ok(ibc_messages)
}
