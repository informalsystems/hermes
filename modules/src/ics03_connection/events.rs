//! Types for the IBC events emitted from Tendermint Websocket for the connection modules.

use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

make_event!(OpenInit, "ibc_connection", "connection_open_init");
make_event!(OpenTry, "ibc_connection", "connection_open_try");
make_event!(OpenAck, "ibc_connection", "connection_open_ack");
make_event!(OpenConfirm, "ibc_connection", "connection_open_confirm");
