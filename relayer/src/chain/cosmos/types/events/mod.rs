use ibc::Height;
use tendermint::abci::Event as AbciEvent;

use crate::event::IbcEventWithHeight;

pub mod channel;
pub mod client;
pub mod connection;

pub fn from_tx_response_event(height: Height, event: &AbciEvent) -> Option<IbcEventWithHeight> {
    // Return the first hit we find
    if let Some(client_res) = client::try_from_tx(event) {
        Some(IbcEventWithHeight::new(client_res, height))
    } else if let Some(conn_res) = connection::try_from_tx(event) {
        Some(IbcEventWithHeight::new(conn_res, height))
    } else {
        channel::try_from_tx(event).map(|chan_res| IbcEventWithHeight::new(chan_res, height))
    }
}
