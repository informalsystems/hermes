//! Types for the IBC events emitted from Tendermint Websocket for the channels modules.

use crate::make_event;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

make_event!(SendPacket, "ibc_channels", "send_packet");
make_event!(RecievePacket, "ibc_channels", "recv_packet");
make_event!(AcknowledgePacket, "ibc_channels", "acknowledge_packet");
make_event!(CleanupPacket, "ibc_channels", "cleanup_packet");
make_event!(TimeoutPacket, "ibc_channels", "timeout_packet");
