use core::time::Duration;

use ibc_relayer_cosmos::types::tendermint::TendermintClientState;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::Height;
use secp256k1::ecdsa::Signature;

pub struct SolomachineConnectionOpenInitPayload {
    pub commitment_prefix: String,
}

pub struct SolomachineConnectionOpenTryPayload {
    pub commitment_prefix: String,
    pub client_state: TendermintClientState,
    pub versions: Vec<Version>,
    pub delay_period: Duration,
    pub update_height: Height,
    pub proof_init: Signature,
    pub proof_client: Signature,
    pub proof_consensus: Signature,
}

pub struct SolomachineConnectionOpenAckPayload {
    pub client_state: TendermintClientState,
    pub version: Version,
    pub update_height: Height,
    pub proof_try: Signature,
    pub proof_client: Signature,
    pub proof_consensus: Signature,
}

pub struct SolomachineConnectionOpenConfirmPayload {}
