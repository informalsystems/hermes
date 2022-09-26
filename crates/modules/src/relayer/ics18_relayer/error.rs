use crate::core::ics24_host::identifier::ClientId;
use crate::core::ics26_routing::error::Error as RoutingError;
use crate::Height;
use flex_error::define_error;

define_error! {
    Error {
        ClientStateNotFound
            { client_id: ClientId }
            | e | { format_args!("client state on destination chain not found, (client id: {0})", e.client_id) },

        ClientAlreadyUpToDate
            {
                client_id: ClientId,
                source_height: Height,
                destination_height: Height,
            }
            | e | {
                format_args!("the client on destination chain is already up-to-date (client id: {0}, source height: {1}, dest height: {2})",
                    e.client_id, e.source_height, e.destination_height)
            },

        ClientAtHigherHeight
            {
                client_id: ClientId,
                source_height: Height,
                destination_height: Height,
            }
            | e | {
                format_args!("the client on destination chain is at a higher height (client id: {0}, source height: {1}, dest height: {2})",
                    e.client_id, e.source_height, e.destination_height)
            },

        TransactionFailed
            [ RoutingError ]
            | _ | { "transaction processing by modules failed" },
    }
}
