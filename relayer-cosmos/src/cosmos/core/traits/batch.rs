use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use std::sync::{Arc, Mutex};
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::core::error::Error;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::chain::CosmosChainContext;

pub trait CosmosChainWithBatch: CosmosChain {
    fn batch_sender(
        &self,
    ) -> &mpsc::UnboundedSender<(
        Vec<OfaMessage<CosmosChainContext<Self>>>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )>;

    fn batch_receiver(
        &self,
    ) -> &Arc<
        Mutex<
            mpsc::UnboundedReceiver<(
                Vec<OfaMessage<CosmosChainContext<Self>>>,
                oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
            )>,
        >,
    >;
}
