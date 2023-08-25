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

// #[async_trait]
// impl CanBuildUpdateClientMessage<MockCosmosRelay, SourceTarget> for MockCosmosRelay {
//     async fn build_update_client_messages(
//         &self,
//         target: SourceTarget,
//         height: &Height,
//     ) -> Result<Vec<Any>, Error> {
//         unimplemented!()
//     }
// }

// #[async_trait]
// impl CanBuildUpdateClientMessage<MockCosmosRelay, DestinationTarget> for MockCosmosRelay {
//     async fn build_update_client_messages(
//         &self,
//         target: DestinationTarget,
//         height: &Height,
//     ) -> Result<Vec<Any>, Error> {
//         unimplemented!()
//     }
// }

// #[async_trait]
// impl CanSendIbcMessages<SourceTarget> for MockCosmosRelay {
//     async fn send_messages(
//         &self,
//         _target: SourceTarget,
//         messages: Vec<Any>,
//     ) -> Result<Vec<Vec<IbcEvent>>, Error> {
//         <IbcMessageSender as IbcMessageSender<MockCosmosRelay, SourceTarget>>::send_messages(
//             self, messages,
//         )
//         .await
//     }
// }

// #[async_trait]
// impl CanSendIbcMessages<DestinationTarget> for MockCosmosRelay {
//     async fn send_messages(
//         &self,
//         _target: DestinationTarget,
//         messages: Vec<MsgEnvelope>,
//     ) -> Result<Vec<Vec<IbcEvent>>, Error> {
//         <IbcMessageSender as IbcMessageSender<MockCosmosRelay, DestinationTarget>>::send_messages(
//             self, messages,
//         )
//         .await
//     }
// }

// #[async_trait]
// impl CanRelayAckPacket for MockCosmosRelay {
//     async fn relay_ack_packet(
//         &self,
//         destination_height: &Height,
//         packet: &Packet,
//         ack: &WriteAcknowledgement,
//     ) -> Result<(), Error> {
//         AckPacketRelayer::relay_ack_packet(self, destination_height, packet, ack).await
//     }
// }

// #[async_trait]
// impl CanRelayReceivePacket for MockCosmosRelay {
//     async fn relay_receive_packet(
//         &self,
//         source_height: &Height,
//         packet: &Packet,
//     ) -> Result<Option<WriteAcknowledgement>, Error> {
//         ReceivePacketRelayer::relay_receive_packet(self, source_height, packet).await
//     }
// }

// #[async_trait]
// impl CanRelayTimeoutUnorderedPacket for MockCosmosRelay {
//     async fn relay_timeout_unordered_packet(
//         &self,
//         destination_height: &Height,
//         packet: &Packet,
//     ) -> Result<(), Self::Error> {
//         TimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
//             self,
//             destination_height,
//             packet,
//         )
//         .await
//     }
// }

// #[async_trait]
// impl CanRelayPacket for MockCosmosRelay {
//     async fn relay_packet(&self, packet: &Packet) -> Result<(), Error> {
//         PacketRelayer::relay_packet(self, packet).await
//     }
// }

// use async_trait::async_trait;
// use eyre::eyre;
// use futures::channel::oneshot::{channel, Sender};
// use ibc::core::ics04_channel::packet::Packet;
// use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId};

// use ibc_relayer_all_in_one::one_for_all::traits::relay::OfaRelay;
// use ibc_relayer_all_in_one::one_for_all::types::batch::aliases::MessageBatchSender;
// use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
// use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
// use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
// use ibc_relayer_runtime::tokio::error::Error as TokioError;
// use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;

// use crate::contexts::chain::MockCosmosChain;
// use crate::contexts::relay::MockCosmosRelay;
// use crate::types::error::{BaseError, Error};

// pub struct PacketLock {
//     pub release_sender: Option<Sender<()>>,
// }

// impl Drop for PacketLock {
//     fn drop(&mut self) {
//         if let Some(sender) = self.release_sender.take() {
//             let _ = sender.send(());
//         }
//     }
// }

// #[async_trait]
// impl OfaRelay for MockCosmosRelay {
//     type Error = Error;

//     type Runtime = TokioRuntimeContext;

//     type Logger = TracingLogger;

//     type Packet = Packet;

//     type SrcChain = MockCosmosChain;

//     type DstChain = MockCosmosChain;

//     type PacketLock<'a> = PacketLock;

//     fn runtime_error(e: TokioError) -> Error {
//         BaseError::tokio(e).into()
//     }

//     fn src_chain_error(e: Error) -> Error {
//         e
//     }

//     fn dst_chain_error(e: Error) -> Error {
//         e
//     }

//     fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
//         &self.runtime
//     }

//     fn logger(&self) -> &TracingLogger {
//         &TracingLogger
//     }

//     fn src_client_id(&self) -> &ClientId {
//         &self.src_client_id
//     }

//     fn dst_client_id(&self) -> &ClientId {
//         &self.dst_client_id
//     }

//     fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
//         &self.src_chain
//     }

//     fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
//         &self.dst_chain
//     }

//     async fn try_acquire_packet_lock<'a>(&'a self, packet: &'a Packet) -> Option<PacketLock> {
//         let packet_key = (
//             packet.source_channel.clone(),
//             packet.source_port.clone(),
//             packet.destination_channel.clone(),
//             packet.destination_port.clone(),
//             packet.sequence,
//         );

//         let mutex = &self.packet_lock_mutex;

//         let mut lock_table = mutex.lock().await;

//         if lock_table.contains(&packet_key) {
//             None
//         } else {
//             lock_table.insert(packet_key.clone());

//             let runtime = &self.runtime().runtime.runtime;

//             let (sender, receiver) = channel();

//             let mutex = mutex.clone();

//             runtime.spawn(async move {
//                 let _ = receiver.await;
//                 let mut lock_table = mutex.lock().await;
//                 lock_table.remove(&packet_key);
//             });

//             Some(PacketLock {
//                 release_sender: Some(sender),
//             })
//         }
//     }

//     fn is_retryable_error(_: &Error) -> bool {
//         false
//     }

//     fn max_retry_exceeded_error(e: Error) -> Error {
//         e
//     }

//     fn missing_connection_init_event_error(&self) -> Error {
//         BaseError::generic(eyre!("missing_connection_init_event_error")).into()
//     }

//     fn missing_src_create_client_event_error(
//         src_chain: &Self::SrcChain,
//         dst_chain: &Self::DstChain,
//     ) -> Self::Error {
//         BaseError::generic(eyre!("missing CreateClient event when creating client from chain {} with counterparty chain {}",
//             src_chain.chain_id(),
//             dst_chain.chain_id(),
//         )).into()
//     }

//     fn missing_dst_create_client_event_error(
//         dst_chain: &Self::DstChain,
//         src_chain: &Self::SrcChain,
//     ) -> Self::Error {
//         BaseError::generic(eyre!("missing CreateClient event when creating client from chain {} with counterparty chain {}",
//             dst_chain.chain_id(),
//             src_chain.chain_id(),
//         )).into()
//     }

//     fn missing_connection_try_event_error(&self, src_connection_id: &ConnectionId) -> Error {
//         BaseError::generic(eyre!(
//             "missing_connection_try_event_error: {}",
//             src_connection_id
//         ))
//         .into()
//     }

//     fn missing_channel_init_event_error(&self) -> Error {
//         BaseError::generic(eyre!("missing_channel_init_event_error")).into()
//     }

//     fn missing_channel_try_event_error(&self, src_channel_id: &ChannelId) -> Error {
//         BaseError::generic(eyre!("missing_channel_try_event_error: {}", src_channel_id)).into()
//     }

//     async fn should_relay_packet(&self, packet: &Packet) -> Result<bool, Error> {
//         unimplemented!()
//     }

//     fn src_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error> {
//         unimplemented!()
//     }

//     fn dst_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error> {
//         unimplemented!()
//     }
// }
