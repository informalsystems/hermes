use flex_error::define_error;

use crate::signer::SignerError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidRawMisbehaviour
            { reason: String }
            | e | { format_args!("invalid raw misbehaviour: {}", e.reason) },

        InvalidRawDoubleVoting
            { reason: String }
            | e | { format_args!("invalid raw double voting: {}", e.reason) },

        Signer
            [ SignerError ]
            | _ | { "failed to parse signer" },
    }
}
