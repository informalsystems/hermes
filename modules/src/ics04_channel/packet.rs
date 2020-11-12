use crate::ics04_channel::error::Error;

// TODO: Packet needs to be implemented
// This is only a workaround for MsgPacket for now!
// https://github.com/informalsystems/ibc-rs/issues/95

#[derive(Clone, Debug, PartialEq)]
pub struct Packet;

impl Packet {
    pub fn validate(&self) -> Result<Packet, Error> {
        Ok(self.clone())
    }
}
