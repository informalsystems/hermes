use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::full::batch::impls::spawn::BatchMessageWorkerSpawner;
use ibc_relayer_framework::full::batch::traits::spawn::CanSpawnBatchMessageWorker;
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use tokio::sync::mpsc::unbounded_channel;
use tokio::sync::Mutex;

use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::contexts::full::chain::FullCosmosChainContext;
use crate::full::traits::relay::CosmosFullRelay;
use crate::full::types::batch::{CosmosBatchReceiver, CosmosBatchSender};

#[derive(Clone)]
pub struct FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: CosmosChain,
    DstChain: CosmosChain,
{
    pub src_chain: Arc<SrcChain>,
    pub dst_chain: Arc<DstChain>,
    pub src_to_dst_client: ForeignClient<
        <DstChain as CosmosChain>::ChainHandle,
        <SrcChain as CosmosChain>::ChainHandle,
    >,
    pub dst_to_src_client: ForeignClient<
        <SrcChain as CosmosChain>::ChainHandle,
        <DstChain as CosmosChain>::ChainHandle,
    >,
    pub packet_filter: PacketFilter,
    pub src_chain_message_batch_sender: CosmosBatchSender,
    pub src_chain_message_batch_receiver: CosmosBatchReceiver,
    pub dst_chain_message_batch_sender: CosmosBatchSender,
    pub dst_chain_message_batch_receiver: CosmosBatchReceiver,
}

impl<SrcChain, DstChain> FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: CosmosChain,
    DstChain: CosmosChain,
{
    pub fn new(
        src_chain: Arc<SrcChain>,
        dst_chain: Arc<DstChain>,
        src_to_dst_client: ForeignClient<
            <DstChain as CosmosChain>::ChainHandle,
            <SrcChain as CosmosChain>::ChainHandle,
        >,
        dst_to_src_client: ForeignClient<
            <SrcChain as CosmosChain>::ChainHandle,
            <DstChain as CosmosChain>::ChainHandle,
        >,
        packet_filter: PacketFilter,
    ) -> Self {
        let (src_chain_message_batch_sender, src_chain_message_batch_receiver) =
            unbounded_channel();

        let (dst_chain_message_batch_sender, dst_chain_message_batch_receiver) =
            unbounded_channel();

        let relay = Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            packet_filter,
            src_chain_message_batch_sender,
            src_chain_message_batch_receiver: Arc::new(Mutex::new(
                src_chain_message_batch_receiver,
            )),
            dst_chain_message_batch_sender,
            dst_chain_message_batch_receiver: Arc::new(Mutex::new(
                dst_chain_message_batch_receiver,
            )),
        };

        relay
    }
}

pub fn new_relay_context_with_batch<SrcChain, DstChain>(
    runtime: TokioRuntimeContext,
    src_chain: FullCosmosChainContext<SrcChain>,
    dst_chain: FullCosmosChainContext<DstChain>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    packet_filter: PacketFilter,
    batch_config: BatchConfig,
) -> OfaRelayWrapper<
    CosmosRelayWrapper<
        FullCosmosRelay<FullCosmosChainContext<SrcChain>, FullCosmosChainContext<DstChain>>,
    >,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let relay = OfaRelayWrapper::new(CosmosRelayWrapper::new(
        Arc::new(FullCosmosRelay::new(
            Arc::new(src_chain),
            Arc::new(dst_chain),
            src_to_dst_client,
            dst_to_src_client,
            packet_filter,
        )),
        runtime,
    ));

    <BatchMessageWorkerSpawner<SourceTarget>>::spawn_batch_message_worker(
        relay.clone(),
        batch_config.clone(),
    );

    <BatchMessageWorkerSpawner<DestinationTarget>>::spawn_batch_message_worker(
        relay.clone(),
        batch_config,
    );

    relay
}

impl<SrcChain, DstChain, Preset> CosmosRelay for FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: CosmosChain<Preset = Preset>,
    DstChain: CosmosChain<Preset = Preset>,
{
    type Preset = Preset;

    type SrcChain = SrcChain;

    type DstChain = DstChain;

    fn src_chain(&self) -> &Arc<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &Arc<Self::DstChain> {
        &self.dst_chain
    }

    fn src_to_dst_client(
        &self,
    ) -> &ForeignClient<
        <Self::DstChain as CosmosChain>::ChainHandle,
        <Self::SrcChain as CosmosChain>::ChainHandle,
    > {
        &self.src_to_dst_client
    }

    fn dst_to_src_client(
        &self,
    ) -> &ForeignClient<
        <Self::SrcChain as CosmosChain>::ChainHandle,
        <Self::DstChain as CosmosChain>::ChainHandle,
    > {
        &self.dst_to_src_client
    }
}

impl<SrcChain, DstChain, Preset> CosmosFullRelay for FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: CosmosChain<Preset = Preset>,
    DstChain: CosmosChain<Preset = Preset>,
{
    fn packet_filter(&self) -> &PacketFilter {
        &self.packet_filter
    }

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.src_chain_message_batch_sender
    }

    fn src_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver {
        &self.src_chain_message_batch_receiver
    }

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.dst_chain_message_batch_sender
    }

    fn dst_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver {
        &self.dst_chain_message_batch_receiver
    }
}
