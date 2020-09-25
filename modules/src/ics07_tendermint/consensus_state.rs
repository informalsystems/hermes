use chrono::{TimeZone, Utc};
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;

use ibc_proto::ibc::tendermint::ConsensusState as RawConsensusState;

use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::block::Height;
use tendermint::hash::Algorithm;
use tendermint::lite::Header;
use tendermint::lite::SignedHeader;
use tendermint::Hash;
use tendermint_proto::DomainType;

use crate::ics02_client::client_type::ClientType;
use crate::ics07_tendermint::error::{Error, Kind};
use crate::ics23_commitment::commitment::CommitmentRoot;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub height: crate::Height,
    pub timestamp: tendermint::time::Time,
    pub root: CommitmentRoot,
    pub next_validators_hash: Hash,
}

impl ConsensusState {
    pub fn new(
        root: CommitmentRoot,
        height: crate::Height,
        timestamp: tendermint::time::Time,
        next_validators_hash: Hash,
    ) -> Self {
        Self {
            root,
            height,
            timestamp,
            next_validators_hash,
        }
    }
}

impl crate::ics02_client::state::ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn height(&self) -> crate::Height {
        self.height
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        unimplemented!()
    }
}

impl DomainType<RawConsensusState> for ConsensusState {}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    // TODO: Fix height conversion below (which ignores epoch number, hence it's incorrect).
    // Related: https://github.com/informalsystems/ibc-rs/issues/191.
    fn try_from(raw: RawConsensusState) -> Result<Self, Self::Error> {
        let proto_timestamp = raw
            .timestamp
            .ok_or_else(|| Kind::InvalidRawConsensusState.context("missing timestamp"))?;

        Ok(Self {
            root: raw
                .root
                .ok_or_else(|| Kind::InvalidRawConsensusState.context("missing commitment root"))?
                .hash
                .into(),
            height: raw
                .height
                .ok_or_else(|| Kind::InvalidRawConsensusState.context("missing height"))?
                .epoch_height
                .into(),
            timestamp: Utc
                .timestamp(proto_timestamp.seconds, proto_timestamp.nanos as u32)
                .into(),
            next_validators_hash: Hash::new(Algorithm::Sha256, &raw.next_validators_hash)
                .map_err(|e| Kind::InvalidRawConsensusState.context(e.to_string()))?,
        })
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        RawConsensusState {
            timestamp: Some(value.timestamp.to_system_time().unwrap().into()),
            root: Some(ibc_proto::ibc::commitment::MerkleRoot { hash: value.root.0 }),
            height: Some(ibc_proto::ibc::client::Height {
                epoch_number: 0,
                epoch_height: value.height.value(),
            }),
            next_validators_hash: value.next_validators_hash.as_bytes().to_vec(),
        }
    }
}

impl From<SignedHeader<TMCommit, TMHeader>> for ConsensusState {
    fn from(header: SignedHeader<TMCommit, TMHeader>) -> Self {
        Self {
            root: CommitmentRoot::from_bytes(&header.header().app_hash),
            height: Height::from(header.header().height()),
            timestamp: header.header().bft_time(),
            next_validators_hash: header.header().next_validators_hash(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test::test_serialization_roundtrip;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data =
            include_str!("../../tests/support/query/serialization/consensus_state.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data =
            include_str!("../../tests/support/query/serialization/consensus_state_proof.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }
}
