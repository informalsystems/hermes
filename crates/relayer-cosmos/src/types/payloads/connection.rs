use core::time::Duration;

use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes,
};
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::Height;

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
    pub proof_height: Height,
    pub proof_ack: CommitmentProofBytes,
}
