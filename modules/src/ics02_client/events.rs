//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

// use serde_json::Value;
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use serde_derive::{Deserialize, Serialize};
use crate::make_event;

make_event!(CreateClientEvent,"ibc_client","create_client");
make_event!(UpdateClientEvent,"ibc_client","update_client");
make_event!(ClientMisbehaviorEvent,"ibc_client","client_misbehavior");
