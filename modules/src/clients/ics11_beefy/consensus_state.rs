use crate::prelude::*;

use beefy_client::primitives::PartialMmrLeaf;
use beefy_primitives::mmr::{BeefyNextAuthoritySet, MmrLeafVersion};
use codec::Encode;
use core::convert::Infallible;

use serde::Serialize;
use sp_core::H256;
use sp_runtime::SaturatedConversion;
use tendermint::{hash::Algorithm, time::Time, Hash};
use tendermint_proto::google::protobuf as tpb;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::lightclients::beefy::v1::{
    BeefyAuthoritySet, BeefyMmrLeafPartial as RawPartialMmrLeaf,
    ConsensusState as RawConsensusState, ParachainHeader as RawParachainHeader,
};

use crate::clients::ics11_beefy::error::Error;
use crate::clients::ics11_beefy::header::{
    decode_parachain_header, merge_leaf_version, split_leaf_version, ParachainHeader,
};
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics23_commitment::commitment::CommitmentRoot;

pub const IBC_CONSENSUS_ID: [u8; 4] = *b"/IBC";
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsensusState {
    pub timestamp: Time,
    pub root: Vec<u8>,
    pub parachain_header: ParachainHeader,
}

impl ConsensusState {
    pub fn new(root: Vec<u8>, timestamp: Time, parachain_header: ParachainHeader) -> Self {
        Self {
            timestamp,
            root,
            parachain_header,
        }
    }
}

impl crate::core::ics02_client::client_consensus::ConsensusState for ConsensusState {
    type Error = Infallible;

    fn client_type(&self) -> ClientType {
        ClientType::Beefy
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root.into()
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
            root: raw.root,
            timestamp,
            parachain_header,
        })
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        // FIXME: shunts like this are necessary due to
        // https://github.com/informalsystems/tendermint-rs/issues/1053
        let tpb::Timestamp { seconds, nanos } = value.timestamp.into();
        let timestamp = ibc_proto::google::protobuf::Timestamp { seconds, nanos };

        RawConsensusState {
            timestamp: Some(timestamp),
            root: value.root,
            parachain_header: Some(RawParachainHeader {
                parachain_header: value.parachain_header.encode(),
                mmr_leaf_partial: Some(RawPartialMmrLeaf {
                    version: {
                        let (major, minor) =
                            value.parachain_header.partial_mmr_leaf.version.split();
                        merge_leaf_version(major, minor) as u32
                    },
                    parent_number: value
                        .parachain_header
                        .partial_mmr_leaf
                        .parent_number_and_hash
                        .0,
                    parent_hash: value
                        .parachain_header
                        .partial_mmr_leaf
                        .parent_number_and_hash
                        .1
                        .encode(),
                    beefy_next_authority_set: Some(BeefyAuthoritySet {
                        id: value
                            .parachain_header
                            .partial_mmr_leaf
                            .beefy_next_authority_set
                            .id,
                        len: value
                            .parachain_header
                            .partial_mmr_leaf
                            .beefy_next_authority_set
                            .len,
                        authority_root: value
                            .parachain_header
                            .partial_mmr_leaf
                            .beefy_next_authority_set
                            .root
                            .encode(),
                    }),
                }),
                para_id: value.parachain_header.para_id,
                parachain_heads_proof: value
                    .parachain_header
                    .parachain_heads_proof
                    .into_iter()
                    .map(|item| item.encode())
                    .collect(),
                heads_leaf_index: value.parachain_header.heads_leaf_index,
                heads_total_count: value.parachain_header.heads_total_count,
                extrinsic_proof: value.parachain_header.extrinsic_proof,
            }),
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
                .into_iter()
                .filter_map(|digest| digest.as_consensus())
                .find(|(id, value)| id == &IBC_CONSENSUS_ID)
                .map(|(.., root)| root.to_vec())
                .unwrap_or_default()
        };

        Self {
            root,
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
    use test_log::test;

    use crate::test::test_serialization_roundtrip;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data =
            include_str!("../../../tests/support/query/serialization/consensus_state.json");
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data =
            include_str!("../../../tests/support/query/serialization/consensus_state_proof.json");
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }
}
