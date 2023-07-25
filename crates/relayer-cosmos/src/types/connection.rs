use core::time::Duration;

use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::proofs::Proofs;

#[derive(Default)]
pub struct CosmosInitConnectionOptions {
    pub delay_period: Duration,
    pub connection_version: Version,
}

pub struct CosmosConnectionOpenInitPayload {
    pub commitment_prefix: CommitmentPrefix,
}

pub struct CosmosConnectionOpenTryPayload {
    pub commitment_prefix: CommitmentPrefix,
    pub proofs: Proofs,
    pub client_state: ClientState,
    pub versions: Vec<Version>,
    pub delay_period: Duration,
}

pub struct CosmosConnectionOpenAckPayload {
    pub client_state: ClientState,
    pub proofs: Proofs,
    pub version: Version,
}

pub struct CosmosConnectionOpenConfirmPayload {
    pub proofs: Proofs,
}

pub struct CosmosConnectionOpenInitEvent {
    pub connection_id: ConnectionId,
}

pub struct CosmosConnectionOpenTryEvent {
    pub connection_id: ConnectionId,
}
