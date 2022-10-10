use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::base::one_for_all::traits::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::full::batch::config::BatchConfig;
use ibc_relayer_framework::full::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};

use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::base::types::runtime::CosmosRuntimeContext;
use crate::contexts::full::chain::CosmosChainContext;
use crate::full::traits::relay::CosmosFullRelay;

#[derive(Clone)]
pub struct CosmosRelayContext<SrcChain, DstChain>
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
}

impl<SrcChain, DstChain> CosmosRelayContext<SrcChain, DstChain>
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
        let relay = Self {
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
            packet_filter,
        };

        relay
    }
}

pub fn new_relay_context_with_batch<SrcChain, DstChain>(
    runtime: CosmosRuntimeContext,
    src_chain: CosmosChainContext<SrcChain>,
    dst_chain: CosmosChainContext<DstChain>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    packet_filter: PacketFilter,
    batch_config: BatchConfig,
) -> OfaRelayWrapper<
    CosmosRelayWrapper<
        CosmosRelayContext<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>>,
    >,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let relay = OfaRelayWrapper::new(CosmosRelayWrapper::new(
        Arc::new(CosmosRelayContext::new(
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

impl<SrcChain, DstChain, Components> CosmosRelay for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: CosmosChain<Components = Components>,
    DstChain: CosmosChain<Components = Components>,
{
    type Components = Components;

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

impl<SrcChain, DstChain, Components> CosmosFullRelay for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: CosmosChain<Components = Components>,
    DstChain: CosmosChain<Components = Components>,
{
    fn packet_filter(&self) -> &PacketFilter {
        &self.packet_filter
    }
}
