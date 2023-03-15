use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use futures::channel::oneshot::Sender as SenderOnce;
use tendermint::abci::Event;

use crate::base::error::Error;
use crate::base::types::message::CosmosIbcMessage;

pub type CosmosBatchPayload = (
    Vec<CosmosIbcMessage>,
    SenderOnce<Result<Vec<Vec<Event>>, Error>>,
);

pub type CosmosBatchSender = UnboundedSender<CosmosBatchPayload>;

pub type CosmosBatchReceiver = UnboundedReceiver<CosmosBatchPayload>;
