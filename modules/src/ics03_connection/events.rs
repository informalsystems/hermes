//! Types for the IBC events emitted from Tendermint Websocket for the connection modules.

use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use serde_derive::{Deserialize, Serialize};
use crate::make_event;

make_event!(ConnectionOpenInitEvent,"ibc_connection","connection_open_init");
make_event!(ConnectionOpenTryEvent,"ibc_connection","connection_open_try");
make_event!(ConnectionOpenAckEvent,"ibc_connection","connection_open_ack");
make_event!(ConnectionOpenConfirmEvent,"ibc_connection","connection_open_confirm");
