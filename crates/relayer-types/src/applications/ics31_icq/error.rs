use crate::core::ics24_host::error::ValidationError as Ics24ValidationError;

use std::prelude::v1::*;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum QueryPacketError {
    #[error("Cannot parse packet content into ABCI Event")]
    PacketParseError {},

    #[error("Event attribute not found: {event}")]
    EventAttributeNotFound {
        event: String
    },

    #[error("ics24 validation error")]
    Ics24Error(Ics24ValidationError),
}

impl From<Ics24ValidationError> for QueryPacketError {
    fn from(error: Ics24ValidationError) -> Self {
        Self::Ics24Error(error)
    }
}