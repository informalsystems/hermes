use alloc::sync::Arc;
use tendermint::abci::Event as AbciEvent;
use tokio::sync::mpsc::{UnboundedReceiver, UnboundedSender};
use tokio::sync::oneshot::Sender as SenderOnce;

use crate::types::error::Error;
use crate::types::message::CosmosIbcMessage;

pub type CosmosBatchPayload = (
    Vec<CosmosIbcMessage>,
    SenderOnce<Result<Vec<Vec<Arc<AbciEvent>>>, Error>>,
);

pub type CosmosBatchSender = UnboundedSender<CosmosBatchPayload>;

pub type CosmosBatchReceiver = UnboundedReceiver<CosmosBatchPayload>;
