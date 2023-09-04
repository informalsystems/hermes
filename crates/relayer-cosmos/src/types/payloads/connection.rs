use core::time::Duration;

use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes,
};
use ibc_relayer_types::proofs::ConsensusProof;
use ibc_relayer_types::Height;

use crate::types::tendermint::TendermintClientState;

#[derive(Debug)]
pub struct CosmosConnectionOpenInitPayload {
    pub commitment_prefix: CommitmentPrefix,
}

#[derive(Debug)]
pub struct CosmosConnectionOpenTryPayload {
    pub commitment_prefix: CommitmentPrefix,
    pub client_state: TendermintClientState,
    pub versions: Vec<Version>,
    pub delay_period: Duration,
    pub update_height: Height,
    pub proof_init: CommitmentProofBytes,
    pub proof_client: CommitmentProofBytes,
    pub proof_consensus: ConsensusProof,
}

#[derive(Debug)]
pub struct CosmosConnectionOpenAckPayload {
    pub client_state: TendermintClientState,
    pub version: Version,
    pub update_height: Height,
    pub proof_try: CommitmentProofBytes,
    pub proof_client: CommitmentProofBytes,
    pub proof_consensus: ConsensusProof,
}

#[derive(Debug)]
pub struct CosmosConnectionOpenConfirmPayload {
    pub update_height: Height,
    pub proof_ack: CommitmentProofBytes,
}
