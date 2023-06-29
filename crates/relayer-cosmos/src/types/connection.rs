use core::time::Duration;

use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;

pub struct CosmosInitConnectionOptions {
    pub delay_period: Duration,
    pub connection_version: Version,
}

pub struct CosmosConnectionOpenInitPayload {
    pub commitment_prefix: CommitmentPrefix,
}
