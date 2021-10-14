//! Definition of domain type msg `MsgUpgradeAnyClient`.

use crate::prelude::*;
use core::convert::TryFrom;
use core::str::FromStr;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;

use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics24_host::identifier::ClientId;
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub(crate) const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpgradeClient";

/// A type of message that triggers the upgrade of an on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpgradeAnyClient {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
    pub proof_upgrade_client: RawMerkleProof,
    pub proof_upgrade_consensus_state: RawMerkleProof,
    pub signer: Signer,
}
impl MsgUpgradeAnyClient {
    pub fn new(
        client_id: ClientId,
        client_state: AnyClientState,
        consensus_state: AnyConsensusState,
        proof_upgrade_client: RawMerkleProof,
        proof_upgrade_consensus_state: RawMerkleProof,
        signer: Signer,
    ) -> Self {
        MsgUpgradeAnyClient {
            client_id,
            client_state,
            consensus_state,
            proof_upgrade_client,
            proof_upgrade_consensus_state,
            signer,
        }
    }
}

mod tests {
    use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;

    use crate::{
        core::{
            ics02_client::{
                client_consensus::AnyConsensusState, client_state::AnyClientState, height::Height,
                msgs::upgrade_client::MsgUpgradeAnyClient,
            },
            ics23_commitment::commitment::test_util::get_dummy_merkle_proof,
            ics24_host::identifier::ClientId,
        },
        mock::{
            client_state::{MockClientState, MockConsensusState},
            header::MockHeader,
        },
        test_utils::get_dummy_account_id,
    };

    #[test]
    fn msg_upgrade_client_serialization() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = get_dummy_account_id();

        let height = Height::new(1, 1);

        let client_state = AnyClientState::Mock(MockClientState(MockHeader::new(height)));
        let consensus_state =
            AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(height)));

        let proof = get_dummy_merkle_proof();

        let msg = MsgUpgradeAnyClient::new(
            client_id,
            client_state,
            consensus_state,
            proof.clone(),
            proof,
            signer,
        );
        let raw: RawMsgUpgradeClient = RawMsgUpgradeClient::from(msg.clone());
        let msg_back = MsgUpgradeAnyClient::try_from(raw.clone()).unwrap();
        let raw_back: RawMsgUpgradeClient = RawMsgUpgradeClient::from(msg_back.clone());
        assert_eq!(msg, msg_back);
        assert_eq!(raw, raw_back);
    }
}
