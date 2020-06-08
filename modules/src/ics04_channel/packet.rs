use serde_derive::{Deserialize, Serialize};
use crate::ics04_channel::error::Error;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Packet;

impl Packet {
    pub fn validate(&self) -> Result<Packet, Error> {
        Ok(self.clone())
    }
}