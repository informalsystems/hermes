use ibc_relayer_framework::full::batch::context::BatchChannel;
use std::sync::{Arc, Mutex};
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::base::error::Error;
use crate::cosmos::base::types::message::CosmosIbcMessage;

pub type CosmosBatchPayload = (
    Vec<CosmosIbcMessage>,
    oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
);

pub type CosmosBatchSender = mpsc::UnboundedSender<CosmosBatchPayload>;

pub type CosmosBatchReceiver = Arc<Mutex<mpsc::UnboundedReceiver<CosmosBatchPayload>>>;

pub type CosmosBatchChannel = BatchChannel<CosmosBatchSender, CosmosBatchReceiver>;
