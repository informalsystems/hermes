use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use std::sync::{Arc, Mutex};
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::core::error::Error;
use crate::cosmos::core::types::chain::CosmosChainContext;

pub type BatchPayload<Chain> = (
    Vec<OfaMessage<CosmosChainContext<Chain>>>,
    oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
);

pub type BatchSender<Chain> = mpsc::UnboundedSender<BatchPayload<Chain>>;

pub type BatchReceiver<Chain> = Arc<Mutex<mpsc::UnboundedReceiver<BatchPayload<Chain>>>>;
