use core::time::Duration;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasConnectionVersionType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionVersion: Async;
}

pub trait HasConnectionStateType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionState: Async;

    fn is_connection_state_init(connection_state: &Self::ConnectionState) -> bool;

    fn is_connection_state_try_open(connection_state: &Self::ConnectionState) -> bool;

    fn is_connection_state_open(connection_state: &Self::ConnectionState) -> bool;
}

pub trait HasConnectionDetailsType<Counterparty>: HasIbcChainTypes<Counterparty> {
    type ConnectionDetails: Async;
}

pub trait HasConnectionDetailsFields<Counterparty>:
    HasConnectionDetailsType<Counterparty>
    + HasConnectionStateType<Counterparty>
    + HasConnectionVersionType<Counterparty>
{
    fn connection_details_state(connection: &Self::ConnectionDetails) -> &Self::ConnectionState;

    fn connection_details_delay(connection: &Self::ConnectionDetails) -> Duration;

    fn connection_details_versions(
        connection: &Self::ConnectionDetails,
    ) -> &[Self::ConnectionVersion];
}
