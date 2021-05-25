//! Definition of domain type msg `MsgUpgradeAnyClient`.

use std::convert::TryFrom;
use std::str::FromStr;

use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
//as RawMerkleProof;

use crate::ics02_client::client_consensus::AnyConsensusState;
use crate::ics02_client::client_state::AnyClientState;
use crate::ics02_client::error::Kind;
use crate::ics23_commitment::commitment::CommitmentProofBytes;
use crate::ics24_host::identifier::ClientId;
use crate::signer::Signer;
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
    pub signer: Signer,
}

impl Msg for MsgUpgradeAnyClient {
    type ValidationError = crate::ics24_host::error::ValidationError;
    type Raw = RawMsgUpgradeClient;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgUpgradeClient> for MsgUpgradeAnyClient {}

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
            signer: dm_msg.signer.to_string(),
        }
    }
}

impl TryFrom<RawMsgUpgradeClient> for MsgUpgradeAnyClient {
    type Error = Kind;

    fn try_from(proto_msg: RawMsgUpgradeClient) -> Result<Self, Self::Error> {
        let raw_client_state = proto_msg.client_state.ok_or(Kind::InvalidRawClientState)?;
        let raw_consensus_state = proto_msg
            .consensus_state
            .ok_or(Kind::InvalidRawConsensusState)?;

        let c_bytes = CommitmentProofBytes::from(proto_msg.proof_upgrade_client);
        let cs_bytes = CommitmentProofBytes::from(proto_msg.proof_upgrade_consensus_state);

        Ok(MsgUpgradeAnyClient {
            client_id: ClientId::from_str(&proto_msg.client_id)
                .map_err(|e| Kind::InvalidClientIdentifier(e.kind().clone()))?,
            client_state: AnyClientState::try_from(raw_client_state)
                .map_err(|_| Kind::InvalidRawClientState)?,
            consensus_state: AnyConsensusState::try_from(raw_consensus_state)
                .map_err(|_| Kind::InvalidRawConsensusState)?,
            proof_upgrade_client: MerkleProof::try_from(c_bytes)
                .map_err(|e| Kind::InvalidUpgradeClientProof(e.kind().clone()))?,
            proof_upgrade_consensus_state: MerkleProof::try_from(cs_bytes)
                .map_err(|e| Kind::InvalidUpgradeConsensusStateProof(e.kind().clone()))?,
            signer: proto_msg.signer.into(),
        })
    }
}

#[cfg(test)]
pub mod test_util {
    use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;
    //use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::{ics02_client::{client_consensus::AnyConsensusState, client_state::AnyClientState, height::Height}, ics24_host::identifier::ClientId, mock::{client_state::{MockClientState, MockConsensusState}, header::MockHeader}, test_utils::{get_dummy_bech32_account, get_dummy_proof}};
    use super::MsgUpgradeAnyClient;


    /// Extends the implementation with additional helper methods.
    impl MsgUpgradeAnyClient {
        /// Setter for `client_id`. Amenable to chaining, since it consumes the input message.
        pub fn with_client_id(self, client_id: ClientId) -> Self {
            MsgUpgradeAnyClient { client_id, ..self }
        }
    }
    
    /// Returns a dummy `RawMsgAcknowledgement`, for testing only!
    /// The `height` parametrizes both the proof height as well as the timeout height.
    pub fn get_dummy_raw_msg_upgrade_client(height :Height) -> RawMsgUpgradeClient {
        RawMsgUpgradeClient {
            client_id: "tendermint".parse().unwrap(),
            client_state: Some(AnyClientState::Mock(MockClientState(MockHeader::new(
                height))).into()),
            consensus_state: Some(AnyConsensusState::Mock(MockConsensusState(MockHeader::new(
                height))).into()),
            proof_upgrade_client: get_dummy_proof(),
            proof_upgrade_consensus_state: get_dummy_proof(),
            signer: get_dummy_bech32_account(),
        }
    }
}