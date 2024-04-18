//! Definition of domain type msg `MsgUpgradeAnyClient`.

use std::str::FromStr;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
use ibc_proto::Protobuf;

use crate::core::ics02_client::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics23_commitment::error::Error as Ics23Error;
use crate::core::ics24_host::identifier::ClientId;
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub(crate) const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpgradeClient";

/// A type of message that triggers the upgrade of an on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpgradeClient {
    pub client_id: ClientId,
    pub client_state: Any,
    pub consensus_state: Any,
    pub proof_upgrade_client: RawMerkleProof,
    pub proof_upgrade_consensus_state: RawMerkleProof,
    pub signer: Signer,
}

impl MsgUpgradeClient {
    pub fn new(
        client_id: ClientId,
        client_state: Any,
        consensus_state: Any,
        proof_upgrade_client: RawMerkleProof,
        proof_upgrade_consensus_state: RawMerkleProof,
        signer: Signer,
    ) -> Self {
        MsgUpgradeClient {
            client_id,
            client_state,
            consensus_state,
            proof_upgrade_client,
            proof_upgrade_consensus_state,
            signer,
        }
    }
}

impl Msg for MsgUpgradeClient {
    type ValidationError = crate::core::ics24_host::error::ValidationError;
    type Raw = RawMsgUpgradeClient;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgUpgradeClient> for MsgUpgradeClient {}

impl From<MsgUpgradeClient> for RawMsgUpgradeClient {
    fn from(dm_msg: MsgUpgradeClient) -> RawMsgUpgradeClient {
        let c_bytes = CommitmentProofBytes::try_from(dm_msg.proof_upgrade_client)
            .map_or(vec![], |c| c.into());
        let cs_bytes = CommitmentProofBytes::try_from(dm_msg.proof_upgrade_consensus_state)
            .map_or(vec![], |c| c.into());

        RawMsgUpgradeClient {
            client_id: dm_msg.client_id.to_string(),
            client_state: Some(dm_msg.client_state),
            consensus_state: Some(dm_msg.consensus_state),
            proof_upgrade_client: c_bytes,
            proof_upgrade_consensus_state: cs_bytes,
            signer: dm_msg.signer.to_string(),
        }
    }
}

impl TryFrom<RawMsgUpgradeClient> for MsgUpgradeClient {
    type Error = Error;

    fn try_from(proto_msg: RawMsgUpgradeClient) -> Result<Self, Self::Error> {
        let raw_client_state = proto_msg
            .client_state
            .ok_or_else(Error::missing_raw_client_state)?;

        let raw_consensus_state = proto_msg
            .consensus_state
            .ok_or_else(Error::missing_raw_client_state)?;

        let c_bytes = CommitmentProofBytes::try_from(proto_msg.proof_upgrade_client)
            .map_err(|_| Error::invalid_upgrade_client_proof(Ics23Error::empty_merkle_proof()))?;
        let cs_bytes = CommitmentProofBytes::try_from(proto_msg.proof_upgrade_consensus_state)
            .map_err(|_| {
                Error::invalid_upgrade_consensus_state_proof(Ics23Error::empty_merkle_proof())
            })?;

        Ok(MsgUpgradeClient {
            client_id: ClientId::from_str(&proto_msg.client_id)
                .map_err(Error::invalid_client_identifier)?,
            client_state: raw_client_state,
            consensus_state: raw_consensus_state,
            proof_upgrade_client: RawMerkleProof::try_from(c_bytes)
                .map_err(Error::invalid_upgrade_client_proof)?,
            proof_upgrade_consensus_state: RawMerkleProof::try_from(cs_bytes)
                .map_err(Error::invalid_upgrade_consensus_state_proof)?,
            signer: proto_msg.signer.parse().map_err(Error::signer)?,
        })
    }
}
