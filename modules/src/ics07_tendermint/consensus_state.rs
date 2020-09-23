use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::commitment::CommitmentRoot;

use crate::ics07_tendermint::error::{Error, Kind};
use crate::try_from_raw::TryFromRaw;
use chrono::{TimeZone, Utc};
use serde_derive::{Deserialize, Serialize};
use tendermint::hash::Algorithm;
use tendermint::Hash;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub height: crate::Height,
    pub timestamp: tendermint::time::Time,
    pub root: CommitmentRoot,
    pub next_validators_hash: Hash,
}

impl TryFromRaw for ConsensusState {
    type RawType = ibc_proto::ibc::tendermint::ConsensusState;
    type Error = Error;

    // TODO: Fix height conversion below (which ignores epoch number, hence it's incorrect).
    // Related: https://github.com/informalsystems/ibc-rs/issues/191.
    fn try_from(raw: Self::RawType) -> Result<Self, Self::Error> {
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
