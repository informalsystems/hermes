use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_framework::addons::batch::config::BatchConfig;
use ibc_relayer_framework::addons::batch::spawn::{
    BatchMessageWorkerSpawner, CanSpawnBatchMessageWorker,
};
use ibc_relayer_framework::core::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;
use crate::cosmos::context::runtime::CosmosRuntimeContext;
use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

impl<Handle> CosmosChainContext<Handle> {}

impl<SrcChain, DstChain> CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    pub fn new_with_batch(
        runtime: CosmosRuntimeContext,
        src_handle: CosmosChainContext<SrcChain>,
        dst_handle: CosmosChainContext<DstChain>,
        src_to_dst_client: ForeignClient<DstChain, SrcChain>,
        dst_to_src_client: ForeignClient<SrcChain, DstChain>,
        batch_config: BatchConfig,
        src_receiver: mpsc::Receiver<(
            Vec<CosmosIbcMessage>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
        dst_receiver: mpsc::Receiver<(
            Vec<CosmosIbcMessage>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    ) -> OfaRelayContext<Self> {
        let relay = Self::new(
            runtime,
            src_handle,
            dst_handle,
            src_to_dst_client,
            dst_to_src_client,
        );

        let context = OfaRelayContext::new(relay);

        <BatchMessageWorkerSpawner<SourceTarget>>::spawn_batch_message_worker(
            context.clone(),
            batch_config.clone(),
            src_receiver,
        );

        <BatchMessageWorkerSpawner<DestinationTarget>>::spawn_batch_message_worker(
            context.clone(),
            batch_config,
            dst_receiver,
        );

        context
    }
}
