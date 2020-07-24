use crate::events::{IBCEvent, RawObject};
use crate::make_event;
use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;

// TODO - extract attributes
make_event!(Timeout, "timeout");
make_event!(Packet, "transfer");
make_event!(ChannelClosed, "channel_closed");

impl From<ChannelClosed> for IBCEvent {
    fn from(v: ChannelClosed) -> Self {
        IBCEvent::ChannelClosedTransfer(v)
    }
}

impl From<Packet> for IBCEvent {
    fn from(v: Packet) -> Self {
        IBCEvent::PacketTransfer(v)
    }
}
impl From<Timeout> for IBCEvent {
    fn from(v: Timeout) -> Self {
        IBCEvent::TimeoutTransfer(v)
    }
}
