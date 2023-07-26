use core::time::Duration;

use ibc_relayer_types::core::ics03_connection::version::Version;

#[derive(Default)]
pub struct CosmosInitConnectionOptions {
    pub delay_period: Duration,
    pub connection_version: Version,
}
