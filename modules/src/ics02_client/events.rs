//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

// use serde_json::Value;
use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

make_event!(CreateClient, "ibc_client", "create_client");
make_event!(UpdateClient, "ibc_client", "update_client");
make_event!(ClientMisbehavior, "ibc_client", "client_misbehavior");
