use crate::application::ics20_fungible_token_transfer;
use crate::ics02_client;
use crate::ics03_connection;
use crate::ics04_channel;
use flex_error::*;
use std::string::String;


define_error! {
    #[derive(Debug)]
    RoutingError {
        Ics02Client
        [ DisplayError<ics02_client::error::ClientError> ]
        | _ | { format_args!("ICS02 client error")},

        Ics03Connection
        [ DisplayError<ics03_connection::error::ConnectionError> ]
        | _ | { format_args!("ICS03 connection error") },

        Ics04Channel
        [ DisplayError<ics04_channel::error::ChannelError>]
        | _ | { format_args!("ICS04 channel error") },

        Ics20FungibleTokenTransfer
        [ DisplayError<ics20_fungible_token_transfer::error::FungibleTokenTransferError>]
        | _ | { format_args!("ICS20 fungible token transfer error") },

        UnknowMessageTypeUrl
        { url: String }
        | e | { format_args!("unknown type URL {0}", e.url) },

        MalformedMessageBytes
        [ DisplayError<tendermint_proto::Error> ]
        | _ | { format_args!("the message is malformed and cannot be decode") },
    }
}
