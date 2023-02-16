use tendermint::abci::Event;
use tokio::sync::mpsc::{UnboundedReceiver, UnboundedSender};
use tokio::sync::oneshot::Sender as SenderOnce;
use tokio::sync::Mutex;

use crate::base::error::Error;
use crate::base::types::message::CosmosIbcMessage;

pub type CosmosBatchPayload = (
    Vec<CosmosIbcMessage>,
    SenderOnce<Result<Vec<Vec<Event>>, Error>>,
);

pub type CosmosBatchSender = UnboundedSender<CosmosBatchPayload>;

pub type CosmosBatchReceiver = Mutex<Option<UnboundedReceiver<CosmosBatchPayload>>>;
