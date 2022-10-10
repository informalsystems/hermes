use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::full::batch::config::BatchConfig;
use ibc_relayer_framework::full::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};

use ibc_relayer_framework::base::one_for_all::traits::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::traits::target::{DestinationTarget, SourceTarget};

use crate::cosmos::basic::relay::CosmosRelayEnv;
use crate::cosmos::core::traits::filter::CosmosFilter;
use crate::cosmos::core::types::relay::CosmosRelayWrapper;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::full::chain::CosmosChainEnv;

pub fn new_relay_context_with_batch<SrcChain, DstChain, Filter>(
    runtime: CosmosRuntimeContext,
    src_chain: CosmosChainEnv<SrcChain>,
    dst_chain: CosmosChainEnv<DstChain>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    batch_config: BatchConfig,
    filter: Filter,
) -> OfaRelayWrapper<
    CosmosRelayWrapper<CosmosRelayEnv<CosmosChainEnv<SrcChain>, CosmosChainEnv<DstChain>>, Filter>,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Filter: CosmosFilter + Clone,
{
    let relay = OfaRelayWrapper::new(CosmosRelayWrapper::new(
        Arc::new(CosmosRelayEnv::new(
            Arc::new(src_chain),
            Arc::new(dst_chain),
            src_to_dst_client,
            dst_to_src_client,
        )),
        runtime,
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
