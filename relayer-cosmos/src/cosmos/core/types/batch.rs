use ibc_relayer_framework::addons::batch::context::BatchChannel;
use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use std::sync::{Arc, Mutex};
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::core::error::Error;
use crate::cosmos::core::types::chain::CosmosChainContext;

pub type CosmosBatchPayload<Chain> = (
    Vec<OfaMessage<CosmosChainContext<Chain>>>,
    oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
);

pub type CosmosBatchSender<Chain> = mpsc::UnboundedSender<CosmosBatchPayload<Chain>>;

pub type CosmosBatchReceiver<Chain> =
    Arc<Mutex<mpsc::UnboundedReceiver<CosmosBatchPayload<Chain>>>>;

pub type CosmosBatchChannel<Chain> =
    BatchChannel<CosmosBatchSender<Chain>, CosmosBatchReceiver<Chain>>;
