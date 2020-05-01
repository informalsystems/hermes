//! Types for the IBC events emitted from Tendermint Websocket for the transfer module.

use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

make_event!(Timeout, "timeout");
make_event!(Packet, "transfer");
make_event!(ChannelClosed, "channel_closed");
