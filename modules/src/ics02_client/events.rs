//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

// use serde_json::Value;
use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use std::error::Error;


make_event!(CreateClient, "create_client");
make_event!(UpdateClient, "update_client");
make_event!(ClientMisbehavior, "client_misbehavior");
