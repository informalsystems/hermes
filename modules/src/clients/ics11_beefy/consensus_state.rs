use crate::prelude::*;

use core::convert::Infallible;
use serde::Serialize;
use sp_runtime::SaturatedConversion;
use tendermint::time::Time;
use tendermint_proto::google::protobuf as tpb;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::lightclients::beefy::v1::ConsensusState as RawConsensusState;

use crate::clients::ics11_beefy::error::Error;
use crate::clients::ics11_beefy::header::{decode_timestamp_extrinsic, ParachainHeader};
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

// This is a constant that comes from pallet-ibc
pub const IBC_CONSENSUS_ID: [u8; 4] = *b"/IBC";
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConsensusState {
    pub timestamp: Time,
    pub root: CommitmentRoot,
}

impl ConsensusState {
    pub fn new(root: Vec<u8>, timestamp: Time, parachain_header: ParachainHeader) -> Self {
        Self {
            timestamp,
            root: root.into(),
        }
    }
}

impl crate::core::ics02_client::client_consensus::ConsensusState for ConsensusState {
    type Error = Infallible;

    fn client_type(&self) -> ClientType {
        ClientType::Beefy
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn wrap_any(self) -> AnyConsensusState {
        AnyConsensusState::Beefy(self)
    }
}

impl Protobuf<RawConsensusState> for ConsensusState {}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    fn try_from(raw: RawConsensusState) -> Result<Self, Self::Error> {
        let ibc_proto::google::protobuf::Timestamp { seconds, nanos } = raw
            .timestamp
            .ok_or_else(|| Error::invalid_raw_consensus_state("missing timestamp".into()))?;
        let proto_timestamp = tpb::Timestamp { seconds, nanos };
        let timestamp = proto_timestamp
            .try_into()
            .map_err(|e| Error::invalid_raw_consensus_state(format!("invalid timestamp: {}", e)))?;

        let parachain_header = raw
            .parachain_header
            .ok_or_else(|| Error::invalid_raw_consensus_state("missing parachain header".into()))?;

        let parachain_header = ParachainHeader {
            parachain_header: decode_parachain_header(parachain_header.parachain_header).map_err(
                |_| Error::invalid_raw_consensus_state("invalid parachain header".into()),
            )?,
            partial_mmr_leaf: {
                let partial_leaf = parachain_header.mmr_leaf_partial.ok_or_else(
                    Error::invalid_raw_consensus_state("missing mmr leaf".into()),
                )?;
                PartialMmrLeaf {
                    version: {
                        let (major, minor) =
                            split_leaf_version(partial_leaf.version.saturated_into::<u8>());
                        MmrLeafVersion::new(major, minor)
                    },
                    parent_number_and_hash: (
                        partial_leaf.parent_number,
                        H256::from_slice(&partial_leaf.parent_hash),
                    ),
                    beefy_next_authority_set: {
                        let next_set = partial_leaf.beefy_next_authority_set.ok_or_else(
                            Error::invalid_raw_consensus_state("missing next authority set".into()),
                        )?;
                        BeefyNextAuthoritySet {
                            id: next_set.id,
                            len: next_set.len,
                            root: H256::from_slice(&next_set.authority_root),
                        }
                    },
                }
            },
            para_id: parachain_header.para_id,
            parachain_heads_proof: parachain_header
                .parachain_heads_proof
                .into_iter()
                .map(|item| {
                    let mut dest = [0u8; 32];
                    dest.copy_from_slice(&*item);
                    dest
                })
                .collect(),
            heads_leaf_index: parachain_header.heads_leaf_index,
            heads_total_count: parachain_header.heads_total_count,
            extrinsic_proof: parachain_header.extrinsic_proof,
        };
        Ok(Self {
            root: raw.root.into(),
            timestamp,
        })
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        let tpb::Timestamp { seconds, nanos } = value.timestamp.into();
        let timestamp = ibc_proto::google::protobuf::Timestamp { seconds, nanos };

        RawConsensusState {
            timestamp: Some(timestamp),
            root: value.root.into_vec(),
        }
    }
}

impl From<ParachainHeader> for ConsensusState {
    fn from(header: ParachainHeader) -> Self {
        let root = {
            header
                .parachain_header
                .digest
                .logs
                .iter()
                .filter_map(|digest| digest.as_consensus())
                .find(|(id, _value)| id == &IBC_CONSENSUS_ID)
                .map(|(.., root)| root.to_vec())
                .unwrap_or_default()
        };

        let timestamp = decode_timestamp_extrinsic(&header).unwrap_or_default();
        let duration = core::time::Duration::from_millis(timestamp);
        let timestamp = Timestamp::from_nanoseconds(duration.as_nanos().saturated_into::<u64>())
            .unwrap_or_default()
            .into_tm_time()
            .unwrap();

        Self {
            root: root.into(),
            timestamp,
        }
    }
}

#[cfg(test)]
mod tests {}
