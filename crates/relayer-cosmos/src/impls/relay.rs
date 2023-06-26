use async_trait::async_trait;
use futures::channel::oneshot::{channel, Sender};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_all_in_one::one_for_all::traits::relay::OfaRelay;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::contexts::relay::CosmosRelay;
use crate::types::batch::CosmosBatchSender;
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;

pub struct PacketLock {
    pub release_sender: Option<Sender<()>>,
}

impl Drop for PacketLock {
    fn drop(&mut self) {
        if let Some(sender) = self.release_sender.take() {
            let _ = sender.send(());
        }
    }
}

#[async_trait]
impl<SrcChain, DstChain> OfaRelay for CosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type Packet = Packet;

    type SrcChain = CosmosChain<SrcChain>;

    type DstChain = CosmosChain<DstChain>;

    type PacketLock<'a> = PacketLock;

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn src_chain_error(e: Error) -> Error {
        e
    }

    fn dst_chain_error(e: Error) -> Error {
        e
    }

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    fn src_client_id(&self) -> &ClientId {
        &self.dst_to_src_client.id
    }

    fn dst_client_id(&self) -> &ClientId {
        &self.src_to_dst_client.id
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &Height,
    ) -> Result<Vec<CosmosIbcMessage>, Self::Error> {
        let height = *height;
        let client = self.dst_to_src_client.clone();

        self.runtime
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
        let client = self.src_to_dst_client.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || build_update_client_messages(&client, height))
            .await
            .map_err(BaseError::join)?
    }

    async fn try_acquire_packet_lock<'a>(&'a self, packet: &'a Packet) -> Option<PacketLock> {
        let packet_key = (
            packet.source_channel.clone(),
            packet.source_port.clone(),
            packet.destination_channel.clone(),
            packet.destination_port.clone(),
            packet.sequence,
        );

        let mutex = &self.packet_lock_mutex;

        let mut lock_table = mutex.lock().await;

        if lock_table.contains(&packet_key) {
            None
        } else {
            lock_table.insert(packet_key.clone());

            let runtime = &self.runtime().runtime.runtime;

            let (sender, receiver) = channel();

            let mutex = mutex.clone();

            runtime.spawn(async move {
                let _ = receiver.await;
                let mut lock_table = mutex.lock().await;
                lock_table.remove(&packet_key);
            });

            Some(PacketLock {
                release_sender: Some(sender),
            })
        }
    }

    fn is_retryable_error(_: &Error) -> bool {
        false
    }

    fn max_retry_exceeded_error(e: Error) -> Error {
        e
    }

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Ok(self
            .packet_filter
            .channel_policy
            .is_allowed(&packet.source_port, &packet.source_channel))
    }

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.src_chain_message_batch_sender
    }

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.dst_chain_message_batch_sender
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
