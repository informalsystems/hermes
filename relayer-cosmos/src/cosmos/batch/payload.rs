use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use tendermint::abci::responses::Event;
use tokio::sync::oneshot;

use crate::cosmos::core::error::Error;
use crate::cosmos::core::types::chain::CosmosChainContext;

pub type BatchPayload<Chain> = (
    Vec<OfaMessage<CosmosChainContext<Chain>>>,
    oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
);
