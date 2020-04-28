//! Types for the IBC events emitted from Tendermint Websocket for the transfer module.

use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

make_event!(Timeout, "ibc_transfer", "timeout");
make_event!(Packet, "ibc_transfer", "fungible_token_packet");
make_event!(ChannelClosed, "ibc_transfer", "channel_closed");
