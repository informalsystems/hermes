use crate::core::ics24_host::error::ValidationError as Ics24ValidationError;

use std::prelude::v1::*;
use flex_error::define_error;

define_error! {
    Error {
        Parse
            | _ | { "Failed to parse content" },

        Attribute
            { event: String }
            | e | { format_args!("Event attribute not found: {}", e.event) },

        Ics24
            | _ | { "ics24 validation error" },

        Tendermint
            | _ | { "Tendermint error" },

        Query
            | _ | { "Failed to query data" },

        Proof
            | _ | { "Proof not found" },
    }
}

impl From<Ics24ValidationError> for Error {
    fn from(_: Ics24ValidationError) -> Self {
        Self::ics24()
    }
}