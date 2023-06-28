use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasConnectionOpenTryEvent<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    type ConnectionOpenTryEvent: Async;

    fn try_extract_connection_open_try_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenTryEvent>;

    fn connection_open_try_event_connection_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> Self::ConnectionId;

    fn connection_open_try_event_client_id(event: &Self::ConnectionOpenTryEvent) -> Self::ClientId;

    fn connection_open_try_event_counterparty_connection_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> Counterparty::ConnectionId;

    fn connection_open_try_event_counterparty_client_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> Counterparty::ClientId;
}
