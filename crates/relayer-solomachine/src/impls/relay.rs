use async_trait::async_trait;

use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_all_in_one::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use ibc_relayer_all_in_one::one_for_all::traits::relay::OfaRelay;
use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_all_in_one::one_for_all::types::batch::aliases::MessageBatchSender;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_cosmos::contexts::chain::CosmosChain;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::context::chain::MockSolomachineChainContext;
use crate::context::relay::SolomachineRelay;
use crate::types::chain::SolomachineChainWrapper;

#[async_trait]
impl<SrcChain, DstChain> OfaRelay for SolomachineRelay<SrcChain, DstChain>
where
    SrcChain: OfaIbcChain<DstChain>,
    DstChain: OfaIbcChain<SrcChain>,
{
    type Error = ();

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type Packet = Packet;

    type SrcChain = SolomachineChainWrapper<MockSolomachineChainContext>;

    type DstChain = CosmosChain<BaseChainHandle>;

    type PacketLock<'a> = ();

    fn runtime_error(_e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error {
        todo!()
    }

    fn src_chain_error(_e: <Self::SrcChain as OfaChainTypes>::Error) -> Self::Error {
        todo!()
    }

    fn dst_chain_error(_e: <Self::DstChain as OfaChainTypes>::Error) -> Self::Error {
        todo!()
    }

    fn is_retryable_error(_e: &Self::Error) -> bool {
        todo!()
    }

    fn max_retry_exceeded_error(_e: Self::Error) -> Self::Error {
        todo!()
    }

    fn missing_src_create_client_event_error(
        _src_chain: &Self::SrcChain,
        _dst_chain: &Self::DstChain,
    ) -> Self::Error {
        todo!()
    }

    fn missing_dst_create_client_event_error(
        _dst_chain: &Self::DstChain,
        _src_chain: &Self::SrcChain,
    ) -> Self::Error {
        todo!()
    }

    fn missing_connection_init_event_error(&self) -> Self::Error {
        todo!()
    }

    fn missing_connection_try_event_error(
        &self,
        _src_connection_id: &<Self::SrcChain as OfaChainTypes>::ConnectionId,
    ) -> Self::Error {
        todo!()
    }

    fn missing_channel_init_event_error(&self) -> Self::Error {
        todo!()
    }

    fn missing_channel_try_event_error(
        &self,
        _src_channel_id: &<Self::SrcChain as OfaChainTypes>::ChannelId,
    ) -> Self::Error {
        todo!()
    }

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        todo!()
    }

    fn logger(&self) -> &Self::Logger {
        todo!()
    }

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChainTypes>::ClientId {
        todo!()
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId {
        todo!()
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        todo!()
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        todo!()
    }

    async fn try_acquire_packet_lock<'a>(
        &'a self,
        _packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>> {
        todo!()
    }

    async fn should_relay_packet(&self, _packet: &Self::Packet) -> Result<bool, Self::Error> {
        todo!()
    }

    fn src_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error> {
        todo!()
    }

    fn dst_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error> {
        todo!()
    }
}
