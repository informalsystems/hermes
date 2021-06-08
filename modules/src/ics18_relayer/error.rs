use flex_error::*;

pub type Error = anyhow::Error;

define_error! {RelayerError;

    ClientStateNotFound
    {client_id: crate::ics24_host::identifier::ClientId}
    | e | { format_args!("client state on destination chain not found, (client id: {0})", e.client_id)},

    ClientAlreadyUpToDate
    {client_id: crate::ics24_host::identifier::ClientId, height_left: crate::Height, height_right: crate::Height}
    | e | { format_args!("the client on destination chain is already up-to-date (client id: {0}, source height: {1}, dest height: {2})", e.client_id, e.height_left, e.height_right)},

    ClientAtHigherHeight
    {client_id: crate::ics24_host::identifier::ClientId, height_left: crate::Height, height_right: crate::Height}
    | e | { format_args!("the client on destination chain is at a higher height (client id: {0}, source height: {1}, dest height: {2})", e.client_id, e.height_left, e.height_right)},

    TransactionFailed
    | _ | { format_args!("transaction processing by modules failed")},
}
