use ibc::{events::IbcEvent, Height};
use tendermint::abci::Event as AbciEvent;

use crate::event::IbcEventWithHeight;

pub mod channel;

pub fn from_tx_response_event(height: Height, event: &AbciEvent) -> Option<IbcEventWithHeight> {
    IbcEvent::try_from(event)
        .ok()
        .map(|ibc_event| IbcEventWithHeight::new(ibc_event, height))
}
