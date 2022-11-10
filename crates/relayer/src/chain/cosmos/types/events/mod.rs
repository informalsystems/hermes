use ibc_relayer_types::Height;
use tendermint_rpc::abci::Event as AbciEvent;

use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

pub mod channel;
pub mod fee;

pub fn from_tx_response_event(height: Height, event: &AbciEvent) -> Option<IbcEventWithHeight> {
    ibc_event_try_from_abci_event(event)
        .ok()
        .map(|ibc_event| IbcEventWithHeight::new(ibc_event, height))
}
