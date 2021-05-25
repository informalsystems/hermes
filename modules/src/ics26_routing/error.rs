use crate::application::ics20_fungible_token_transfer;
use crate::ics02_client;
use crate::ics03_connection;
use crate::ics04_channel;
use flex_error::*;
use tendermint_proto;

define_error! { RoutingError;
    Ics02Client
    [ StdError<ics02_client::error::Error> ]
    | _ | { format_args!("error raised by the keeper functionality in message handler") },

    Ics04Channel
    [ StdError<ics04_channel::error::Error> ]
    | _ | { format_args!("error raised by message handler") },

    Ics03Connection
    [ StdError<ics03_connection::error::Error> ]
    | _ | { format_args!("error raised by message handler") },

    Ics20FungibleTokenTransfer
    [ StdError<ics20_fungible_token_transfer::error::Error> ]
    | _ | { format_args!("error raised by message handler") },

    UnknownMessageTypeUrl
    { url: String }
    | e | { format_args!("unknown type URL {0}", e.url) },

    MalformedMessageBytes
    [ StdError<tendermint_proto::Error> ]
    | _ | { format_args!("the message is malformed and cannot be decoded") },
}
