use core::time::Duration;

use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;

#[derive(Default)]
pub struct CosmosInitConnectionOptions {
    pub delay_period: Duration,
    pub connection_version: Version,
}

pub struct CosmosConnectionOpenInitEvent {
    pub connection_id: ConnectionId,
}

pub struct CosmosConnectionOpenTryEvent {
    pub connection_id: ConnectionId,
}
