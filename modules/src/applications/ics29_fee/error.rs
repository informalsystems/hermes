use flex_error::{define_error, TraceError};
use prost::EncodeError;

use crate::applications::transfer::error::Error as TransferError;
use crate::core::ics04_channel::error::Error as ChannelError;
use crate::core::ics24_host::error::ValidationError;
use crate::prelude::*;
use crate::signer::SignerError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Transfer
            [ TransferError ]
            | _ | { "transfer error" },

        Channel
            [ ChannelError ]
            | _ | { "channel error" },

        Signer
            [ SignerError ]
            | _ | { "failed to parse signer" },

        Ics24
            [ ValidationError ]
            | _ | { "ics24 error" },

        EmptyFee
            | _ | { "expect fee field to be non-empty" },

        EmptyPacketId
            | _ | { "expect packet_id field to be non-empty" },

        Encode
            [ TraceError<EncodeError> ]
            | _ | { "protobuf encode error" },

        EventAttributeNotFound
            { key: String }
            | e | { format_args!("IBC event attribute not found for key: {}", e.key) },
    }
}
