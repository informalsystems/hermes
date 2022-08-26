use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::addons::batch::config::BatchConfig;
use ibc_relayer_framework::addons::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};
use ibc_relayer_framework::core::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::context::chain::CosmosChainImpl;
use crate::cosmos::context::relay::CosmosRelayImpl;
use crate::cosmos::context::runtime::CosmosRuntimeContext;
use crate::cosmos::types::relay::CosmosRelayContext;

pub fn new_relay_context_with_batch<SrcChain, DstChain>(
    runtime: CosmosRuntimeContext,
    src_chain: Arc<CosmosChainImpl<SrcChain>>,
    dst_chain: Arc<CosmosChainImpl<DstChain>>,
    src_to_dst_client: ForeignClient<DstChain, SrcChain>,
    dst_to_src_client: ForeignClient<SrcChain, DstChain>,
    batch_config: BatchConfig,
) -> OfaRelayContext<
    CosmosRelayContext<CosmosRelayImpl<CosmosChainImpl<SrcChain>, CosmosChainImpl<DstChain>>>,
>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    let relay = OfaRelayContext::new(CosmosRelayContext::new(
        Arc::new(CosmosRelayImpl::new(
            src_chain,
            dst_chain,
            src_to_dst_client,
            dst_to_src_client,
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
