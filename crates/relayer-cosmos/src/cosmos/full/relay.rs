use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::addons::batch::config::BatchConfig;
use ibc_relayer_framework::addons::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};

use ibc_relayer_framework::core::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::basic::relay::CosmosRelayEnv;
use crate::cosmos::core::traits::filter::CosmosFilter;
use crate::cosmos::core::types::relay::CosmosRelayContext;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;
use crate::cosmos::full::chain::CosmosChainEnv;

pub fn new_relay_context_with_batch<SrcChain, DstChain, Filter>(
    runtime: CosmosRuntimeContext,
    src_chain: CosmosChainEnv<SrcChain>,
    dst_chain: CosmosChainEnv<DstChain>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    batch_config: BatchConfig,
    telemetry: CosmosTelemetry,
    filter: Filter,
) -> OfaRelayContext<
    CosmosRelayContext<CosmosRelayEnv<CosmosChainEnv<SrcChain>, CosmosChainEnv<DstChain>>, Filter>,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Filter: CosmosFilter + Clone,
{
    let relay = OfaRelayContext::new(CosmosRelayContext::new(
        Arc::new(CosmosRelayEnv::new(
            Arc::new(src_chain),
            Arc::new(dst_chain),
            src_to_dst_client,
            dst_to_src_client,
        )),
        runtime,
        telemetry,
        filter,
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
