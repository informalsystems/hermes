use crate::ics04_channel::error::Error;
use serde_derive::{Deserialize, Serialize};

// TODO: Packet needs to be implemented
// This is only a workaround for MsgPacket for now!

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Packet;

impl Packet {
    pub fn validate(&self) -> Result<Packet, Error> {
        Ok(self.clone())
    }
}
