use crate::prelude::*;

use crate::signer::SignerError;
use flex_error::define_error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidRawMisbehaviour
            { reason: String }
            | e | { format_args!("invalid raw misbehaviour: {}", e.reason) },
        Signer
            [ SignerError ]
            | _ | { "failed to parse signer" },
    }
}
