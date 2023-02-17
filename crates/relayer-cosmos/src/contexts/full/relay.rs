use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::base::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::full::batch::types::config::BatchConfig;
use ibc_relayer_framework::full::batch::worker::CanSpawnBatchMessageWorker;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use tokio::sync::mpsc::unbounded_channel;

use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::contexts::full::chain::FullCosmosChainContext;
use crate::full::traits::relay::CosmosFullRelay;
use crate::full::types::batch::CosmosBatchSender;

pub struct FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<SrcChain>>>,
    pub dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<DstChain>>>,
    pub src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    pub dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    pub packet_filter: PacketFilter,
    pub src_chain_message_batch_sender: CosmosBatchSender,
    pub dst_chain_message_batch_sender: CosmosBatchSender,
}

impl<SrcChain, DstChain> FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new(
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<SrcChain>>>,
        dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<DstChain>>>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
        packet_filter: PacketFilter,
        src_chain_message_batch_sender: CosmosBatchSender,
        dst_chain_message_batch_sender: CosmosBatchSender,
    ) -> Self {
        let relay = Self {
            runtime,
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            packet_filter,
            src_chain_message_batch_sender,
            dst_chain_message_batch_sender,
        };

        relay
    }
}

pub fn new_relay_context_with_batch<SrcChain, DstChain>(
    runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    src_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<SrcChain>>>,
    dst_chain: OfaChainWrapper<CosmosChainWrapper<FullCosmosChainContext<DstChain>>>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    packet_filter: PacketFilter,
    batch_config: BatchConfig,
) -> OfaRelayWrapper<CosmosRelayWrapper<FullCosmosRelay<SrcChain, DstChain>>>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let (src_chain_message_batch_sender, src_chain_message_batch_receiver) = unbounded_channel();

    let (dst_chain_message_batch_sender, dst_chain_message_batch_receiver) = unbounded_channel();

    let relay = OfaRelayWrapper::new(CosmosRelayWrapper::new(FullCosmosRelay::new(
        runtime,
        src_chain,
        dst_chain,
        src_to_dst_client,
        dst_to_src_client,
        packet_filter,
        src_chain_message_batch_sender,
        dst_chain_message_batch_sender,
    )));

    relay.clone().spawn_batch_message_worker(
        SourceTarget,
        batch_config.clone(),
        src_chain_message_batch_receiver,
    );

    relay.clone().spawn_batch_message_worker(
        DestinationTarget,
        batch_config,
        dst_chain_message_batch_receiver,
    );

    relay
}

impl<SrcChain, DstChain> CosmosRelay for FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    type Preset = FullPreset;

    type SrcChain = FullCosmosChainContext<SrcChain>;

    type DstChain = FullCosmosChainContext<DstChain>;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn src_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::SrcChain>> {
        &self.src_chain
    }

    fn dst_chain(&self) -> &OfaChainWrapper<CosmosChainWrapper<Self::DstChain>> {
        &self.dst_chain
    }

    fn src_to_dst_client(&self) -> &ForeignClient<DstChain, SrcChain> {
        &self.src_to_dst_client
    }

    fn dst_to_src_client(&self) -> &ForeignClient<SrcChain, DstChain> {
        &self.dst_to_src_client
    }
}

impl<SrcChain, DstChain> CosmosFullRelay for FullCosmosRelay<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    fn packet_filter(&self) -> &PacketFilter {
        &self.packet_filter
    }

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.src_chain_message_batch_sender
    }

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        &self.dst_chain_message_batch_sender
    }
}
