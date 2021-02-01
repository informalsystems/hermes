use std::convert::TryFrom;

use chrono::{TimeZone, Utc};
use serde::Serialize;
use tendermint::{hash::Algorithm, time::Time, Hash};
use tendermint_proto::Protobuf;

use ibc_proto::ibc::lightclients::tendermint::v1::ConsensusState as RawConsensusState;

use crate::ics02_client::{client_def::AnyConsensusState, client_type::ClientType};
use crate::ics07_tendermint::error::{Error, Kind};
use crate::ics07_tendermint::header::Header;
use crate::ics23_commitment::commitment::CommitmentRoot;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConsensusState {
    pub timestamp: Time,
    pub root: CommitmentRoot,
    pub next_validators_hash: Hash,
}

impl ConsensusState {
    pub fn new(root: CommitmentRoot, timestamp: Time, next_validators_hash: Hash) -> Self {
        Self {
            root,
            timestamp,
            next_validators_hash,
        }
    }
}

impl crate::ics02_client::state::ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        unimplemented!()
    }

    fn wrap_any(self) -> AnyConsensusState {
        AnyConsensusState::Tendermint(self)
    }
}

impl Protobuf<RawConsensusState> for ConsensusState {}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

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
            timestamp: Utc
                .timestamp(proto_timestamp.seconds, proto_timestamp.nanos as u32)
                .into(),
            next_validators_hash: Hash::from_bytes(Algorithm::Sha256, &raw.next_validators_hash)
                .map_err(|e| Kind::InvalidRawConsensusState.context(e.to_string()))?,
        })
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        RawConsensusState {
            timestamp: Some(value.timestamp.to_system_time().unwrap().into()),
            root: Some(ibc_proto::ibc::core::commitment::v1::MerkleRoot {
                hash: value.root.into_vec(),
            }),
            next_validators_hash: value.next_validators_hash.as_bytes().to_vec(),
        }
    }
}

impl From<tendermint::block::Header> for ConsensusState {
    fn from(header: tendermint::block::Header) -> Self {
        Self {
            root: CommitmentRoot::from_bytes(header.app_hash.as_ref()),
            timestamp: header.time,
            next_validators_hash: header.next_validators_hash,
        }
    }
}

impl From<Header> for ConsensusState {
    fn from(header: Header) -> Self {
        Self::from(header.signed_header.header)
    }
}

#[cfg(test)]
mod tests {
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    use crate::test::test_serialization_roundtrip;

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
