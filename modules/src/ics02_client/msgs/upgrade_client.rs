//! Definition of domain type msg `MsgUpgradeAnyClient`.

use tendermint::account::Id as AccountId;

use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics23_commitment::commitment::CommitmentProofBytes;
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

pub(crate) const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpgradeClient";

/// A type of message that triggers the upgrade of an on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpgradeAnyClient {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
    pub proof_upgrade_client: MerkleProof,
    pub proof_upgrade_consensus_state: MerkleProof,
}

impl Msg for MsgUpgradeAnyClient {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        unimplemented!()
    }
}

impl From<MsgUpgradeAnyClient> for RawMsgUpgradeClient {
    fn from(dm_msg: MsgUpgradeAnyClient) -> RawMsgUpgradeClient {
        let c_bytes: CommitmentProofBytes = dm_msg.proof_upgrade_client.into();
        let cs_bytes: CommitmentProofBytes = dm_msg.proof_upgrade_consensus_state.into();

        RawMsgUpgradeClient {
            client_id: dm_msg.client_id.to_string(),
            client_state: Some(dm_msg.client_state.into()),
            consensus_state: Some(dm_msg.consensus_state.into()),
            proof_upgrade_client: c_bytes.into(),
            proof_upgrade_consensus_state: cs_bytes.into(),
            signer: "".into(),
        }
    }
}
