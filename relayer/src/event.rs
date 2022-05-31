pub mod bus;
pub mod monitor;
pub mod rpc;

pub(crate) mod ics02_client;
pub(crate) mod ics03_connection;
pub(crate) mod ics04_channel;

use ibc::events::IbcEvent;
use ibc::Height;
use tendermint_rpc::abci;

// This is tendermint specific
pub(crate) fn from_tx_response_event(height: Height, event: &abci::Event) -> Option<IbcEvent> {
    // Return the first hit we find
    if let Some(mut client_res) = ics02_client::try_from_tx(event) {
        client_res.set_height(height);
        Some(client_res)
    } else if let Some(mut conn_res) = ics03_connection::try_from_tx(event) {
        conn_res.set_height(height);
        Some(conn_res)
    } else if let Some(mut chan_res) = ics04_channel::try_from_tx(event) {
        chan_res.set_height(height);
        Some(chan_res)
    } else {
        None
    }
}

#[cfg(test)]
trait ToAbciEvent {
    fn to_abci_event(&self) -> abci::Event;
}
