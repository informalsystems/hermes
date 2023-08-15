use async_trait::async_trait;
use eyre::eyre;
use futures::channel::oneshot::{channel, Sender};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_all_in_one::one_for_all::traits::chain::OfaChain;
use ibc_relayer_all_in_one::one_for_all::traits::relay::OfaRelay;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId};

use crate::contexts::chain::CosmosChain;
use crate::contexts::relay::CosmosRelay;
use crate::types::batch::CosmosBatchSender;
use crate::types::error::{BaseError, Error};

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
        &self.src_client_id
    }

    fn dst_client_id(&self) -> &ClientId {
        &self.dst_client_id
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        &self.dst_chain
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

    fn missing_connection_init_event_error(&self) -> Error {
        BaseError::generic(eyre!("missing_connection_init_event_error")).into()
    }

    fn missing_src_create_client_event_error(
        src_chain: &Self::SrcChain,
        dst_chain: &Self::DstChain,
    ) -> Self::Error {
        BaseError::generic(eyre!("missing CreateClient event when creating client from chain {} with counterparty chain {}",
            src_chain.chain_id(),
            dst_chain.chain_id(),
        )).into()
    }

    fn missing_dst_create_client_event_error(
        dst_chain: &Self::DstChain,
        src_chain: &Self::SrcChain,
    ) -> Self::Error {
        BaseError::generic(eyre!("missing CreateClient event when creating client from chain {} with counterparty chain {}",
            dst_chain.chain_id(),
            src_chain.chain_id(),
        )).into()
    }

    fn missing_connection_try_event_error(&self, src_connection_id: &ConnectionId) -> Error {
        BaseError::generic(eyre!(
            "missing_connection_try_event_error: {}",
            src_connection_id
        ))
        .into()
    }

    fn missing_channel_init_event_error(&self) -> Error {
        BaseError::generic(eyre!("missing_channel_init_event_error")).into()
    }

    fn missing_channel_try_event_error(&self, src_channel_id: &ChannelId) -> Error {
        BaseError::generic(eyre!("missing_channel_try_event_error: {}", src_channel_id)).into()
    }

    async fn should_relay_packet(&self, packet: &Packet) -> Result<bool, Error> {
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
