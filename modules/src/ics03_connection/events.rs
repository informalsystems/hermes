//! Types for the IBC events emitted from Tendermint Websocket for the connection modules.

use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use serde_derive::{Deserialize, Serialize};
use crate::make_event;

make_event!(OpenInitEvent,"ibc_connection","connection_open_init");
make_event!(OpenTryEvent,"ibc_connection","connection_open_try");
make_event!(OpenAckEvent,"ibc_connection","connection_open_ack");
make_event!(OpenConfirmEvent,"ibc_connection","connection_open_confirm");
