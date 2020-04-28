//! Types for the IBC events emitted from Tendermint Websocket for the transfer module.

use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use serde_derive::{Deserialize, Serialize};
use crate::make_event;

make_event!(Timeout,"ibc_transfer","timeout");
make_event!(Packet,"ibc_transfer","fungible_token_packet");
make_event!(ChannelClosed,"ibc_transfer","channel_closed");