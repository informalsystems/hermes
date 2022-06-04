use flex_error::define_error;

use crate::applications::transfer::error::Error as TransferError;
use crate::core::ics04_channel::error::Error as ChannelError;
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

        EmptyFee
            | _ | { "expect fee field to be non-empty" },

        EmptyPacketId
            | _ | { "expect packet_id field to be non-empty" },
    }
}
