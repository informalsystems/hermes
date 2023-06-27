use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasConnectionVersionType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionVersion: Async;
}

pub trait HasConnectionStateType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionState;

    fn is_connection_state_init(connection_state: &Self::ConnectionState) -> bool;

    fn is_connection_state_try_open(connection_state: &Self::ConnectionState) -> bool;

    fn is_connection_state_open(connection_state: &Self::ConnectionState) -> bool;
}

pub trait HasConnectionEndType<Counterparty>: HasConnectionStateType<Counterparty> {
    type ConnectionEnd;

    fn connection_state(connection: &Self::ConnectionEnd) -> &Self::ConnectionState;
}
