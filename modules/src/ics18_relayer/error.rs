use crate::ics24_host::identifier::ClientId;
use crate::Height;
use displaydoc::Display;
use flex_error::*;

pub type Error = anyhow::Error;

define_error! {KindError;

    ClientStateNotFound
    {client_id: ClientId}
    | e | { format_args!("client state on destination chain not found, (client id: {0})", e.client_id)},

    ClientAlreadyUpToDate
    {client_id: ClientId, height_left: Height, height_right: Height}
    | e | { format_args!("the client on destination chain is already up-to-date (client id: {0}, source height: {1}, dest height: {2})", e.client_id, e.height_left, e.height_right)},

    ClientAtHigherHeight
    {client_id: ClientId, height_left: Height, height_right: Height}
    | e | { format_args!("the client on destination chain is at a higher height (client id: {0}, source height: {1}, dest height: {2})", e.client_id, e.height_left, e.height_right)}

    TransactionFailed
    | _ | { format_args!("transaction processing by modules failed")}
}
