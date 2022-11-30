use ibc_relayer_types::Height;
use tendermint::abci;

use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

pub mod channel;
pub mod fee;

pub fn from_tx_response_event(height: Height, event: &abci::Event) -> Option<IbcEventWithHeight> {
    ibc_event_try_from_abci_event(event)
        .ok()
        .map(|ibc_event| IbcEventWithHeight::new(ibc_event, height))
}
