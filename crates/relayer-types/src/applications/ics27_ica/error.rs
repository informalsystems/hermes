use crate::core::ics24_host::error::ValidationError;
use crate::signer::SignerError;

use flex_error::define_error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Owner
        [ SignerError ]
            | _ | { "failed to parse owner" },

        InvalidConnectionIdentifier
        [ ValidationError ]
            | _ | { "connection identifier error" },

        InvalidPacketData
        | _ | { "packet data is None" },

        InvalidRelativeTimeout
        { timestamp: u64 }
        | e | { format_args!("invalid packet timeout timestamp value: `{}`", e.timestamp) },
    }
}
