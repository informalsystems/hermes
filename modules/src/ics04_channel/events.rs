//! Types for the IBC events emitted from Tendermint Websocket for the channels modules.

use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use std::error::Error;

make_event!(SendPacket, "send_packet");
make_event!(RecievePacket, "recv_packet");
make_event!(AcknowledgePacket, "acknowledge_packet");
make_event!(CleanupPacket, "cleanup_packet");
make_event!(TimeoutPacket, "timeout_packet");
make_event!(OpaquePacket, "ics04/opaque");

