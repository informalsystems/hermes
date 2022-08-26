use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use ibc_relayer_framework::one_for_all::traits::batch::OfaChainWithBatch;
use std::sync::Mutex;
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::core::error::Error;
use crate::cosmos::core::traits::batch::CosmosChainWithBatch;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;

impl<Chain> OfaChainWithBatch for CosmosChainContext<Chain>
where
    Chain: CosmosChainWithBatch,
{
    type BatchContext = CosmosRuntimeContext;

    fn batch_sender(
        &self,
    ) -> &mpsc::Sender<(
        Vec<OfaMessage<CosmosChainContext<Chain>>>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )> {
        self.chain.batch_sender()
    }

    fn batch_receiver(
        &self,
    ) -> &Mutex<
        mpsc::Receiver<(
            Vec<OfaMessage<CosmosChainContext<Chain>>>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    > {
        self.chain.batch_receiver()
    }
}
