use prost::Message;
use serde_derive::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use crate::alloc::string::ToString;
use crate::clients::ics11_beefy::client_state::REVISION_NUMBER;
use crate::clients::ics11_beefy::error::Error;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::header::AnyHeader;
use crate::core::ics24_host::identifier::ChainId;
use crate::timestamp::Timestamp;
use crate::Height;
use alloc::vec;
use alloc::vec::Vec;
use beefy_client::primitives::{
    BeefyNextAuthoritySet, Hash, MmrUpdateProof, PartialMmrLeaf, SignatureWithAuthorityIndex,
    SignedCommitment,
};
use beefy_primitives::known_payload_ids::MMR_ROOT_ID;
use beefy_primitives::mmr::{MmrLeaf, MmrLeafVersion};
use beefy_primitives::{Commitment, Payload};
use bytes::Buf;
use codec::{Decode, Encode};
use ibc_proto::ibc::lightclients::beefy::v1::{
    BeefyAuthoritySet as RawBeefyAuthoritySet, BeefyMmrLeaf as RawBeefyMmrLeaf,
    BeefyMmrLeafPartial as RawBeefyMmrLeafPartial, Commitment as RawCommitment,
    CommitmentSignature, Header as RawBeefyHeader, MmrUpdateProof as RawMmrUpdateProof,
    ParachainHeader as RawParachainHeader, PayloadItem as RawPayloadItem, PayloadItem,
    SignedCommitment as RawSignedCommitment,
};
use pallet_mmr_primitives::{BatchProof, Proof};
use sp_core::H256;
use sp_runtime::generic::Header as SubstrateHeader;
use sp_runtime::traits::{BlakeTwo256, SaturatedConversion};
use sp_runtime::Digest;
use sp_trie::TrieDBMut;

/// Beefy consensus header
#[derive(Clone, PartialEq, Eq)]
pub struct BeefyHeader {
    pub parachain_headers: Vec<ParachainHeader>, // contains the parachain headers
    pub mmr_proofs: Vec<Vec<u8>>,                // mmr proofs for these headers
    pub mmr_size: u64,                           // The latest mmr size
    pub mmr_update_proof: Option<MmrUpdateProof>, // Proof for updating the latest mmr root hash
}

#[derive(Clone, PartialEq, Eq, codec::Encode, codec::Decode)]
pub struct ParachainHeader {
    pub parachain_header: SubstrateHeader<u32, H256>,
    /// Reconstructed mmr leaf
    pub partial_mmr_leaf: PartialMmrLeaf,
    /// parachain id
    pub para_id: u32,
    /// Proof for our parachain header inclusion in the parachain headers root
    pub parachain_heads_proof: Vec<Hash>,
    /// leaf index for parachain heads proof
    pub heads_leaf_index: u32,
    /// Total number of parachain heads
    pub heads_total_count: u32,
    /// Trie merkle proof of inclusion of the set timestamp extrinsic in header.extrinsic_root
    /// this already encodes the actual extrinsic
    pub extrinsic_proof: Vec<Vec<u8>>,
}

pub fn split_leaf_version(version: u8) -> (u8, u8) {
    let major = version >> 5;
    let minor = version & 0b11111;
    (major, minor)
}

pub fn merge_leaf_version(major: u8, minor: u8) -> u8 {
    (major << 5) + minor
}

impl TryFrom<RawBeefyHeader> for BeefyHeader {
    type Error = Error;

    fn try_from(raw_header: RawBeefyHeader) -> Result<Self, Self::Error> {
        let parachain_headers = raw_header
            .parachain_headers
            .into_iter()
            .map(|raw_para_header| {
                let parent_hash =
                    H256::decode(&mut raw_para_header.mmr_leaf_partial.parent_hash.as_slice())
                        .unwrap();
                let beefy_next_authority_set = if let Some(next_set) =
                    raw_para_header.mmr_leaf_partial.beefy_next_authority_set
                {
                    BeefyNextAuthoritySet {
                        id: next_set.id,
                        len: next_set.len,
                        root: H256::decode(&mut next_set.root.as_slice()).unwrap(),
                    }
                } else {
                    Default::default()
                };
                Ok(ParachainHeader {
                    parachain_header: decode_parachain_header(raw_para_header.parachain_header)
                        .map_err(|err| Error::invalid_header(err))?,
                    partial_mmr_leaf: PartialMmrLeaf {
                        version: {
                            let (major, minor) = split_leaf_version(
                                raw_para_header
                                    .mmr_leaf_partial
                                    .version
                                    .saturated_into::<u8>(),
                            );
                            MmrLeafVersion::new(major, minor)
                        },
                        parent_number_and_hash: (
                            raw_para_header.mmr_leaf_partial.parent_number,
                            parent_hash,
                        ),
                        beefy_next_authority_set,
                    },
                    para_id: raw_para_header.para_id,
                    parachain_heads_proof: raw_para_header
                        .parachain_heads_proof
                        .into_iter()
                        .map(|item| {
                            let mut dest = [0u8; 32];
                            dest.copy_from_slice(&*item);
                            dest
                        })
                        .collect(),
                    heads_leaf_index: raw_para_header.heads_leaf_index,
                    heads_total_count: raw_para_header.heads_total_count,
                    extrinsic_proof: raw_para_header.extrinsic_proof,
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let mmr_update_proof = if let Some(mmr_update) = raw_header.mmr_update_proof {
            let payload = {
                mmr_update
                    .signed_commitment
                    .as_ref()
                    .unwrap()
                    .commitment
                    .unwrap()
                    .payload
                    .iter()
                    .map(|item| {
                        let mut payload_id = [0u8; 2];
                        payload_id.copy_from_slice(&item.payload_id);
                        Payload::new(payload_id, item.payload_data.clone())
                    })
                    .collect()
            };
            let block_number = mmr_update
                .signed_commitment
                .as_ref()
                .unwrap()
                .commitment
                .unwrap()
                .block_numer;
            let validator_set_id = mmr_update
                .signed_commitment
                .as_ref()
                .unwrap()
                .commitment
                .unwrap()
                .validator_set_id;
            let signatures = mmr_update
                .signed_commitment
                .unwrap()
                .signatures
                .into_iter()
                .map(|commitment_sig| SignatureWithAuthorityIndex {
                    signature: {
                        let mut sig = [0u8; 65];
                        sig.copy_from_slice(&commitment_sig.signature);
                        sig
                    },
                    index: commitment_sig.authority_index,
                })
                .collect();
            Some(MmrUpdateProof {
                signed_commitment: SignedCommitment {
                    commitment: Commitment {
                        payload,
                        block_number,
                        validator_set_id,
                    },
                    signatures,
                },
                latest_mmr_leaf: MmrLeaf {
                    version: {
                        let (major, minor) = split_leaf_version(
                            mmr_update
                                .mmr_leaf
                                .as_ref()
                                .unwrap()
                                .version
                                .saturated_into::<u8>(),
                        );
                        MmrLeafVersion::new(major, minor)
                    },
                    parent_number_and_hash: {
                        let parent_number = mmr_update.mmr_leaf.as_ref().unwrap().parent_number;
                        let parent_hash = H256::decode(
                            &mut mmr_update.mmr_leaf.as_ref().unwrap().parent_hash.as_slice(),
                        )
                        .unwrap();
                        (parent_number, parent_hash)
                    },
                    beefy_next_authority_set: BeefyNextAuthoritySet {
                        id: mmr_update
                            .mmr_leaf
                            .as_ref()
                            .unwrap()
                            .beefy_next_authority_set
                            .unwrap()
                            .id,
                        len: mmr_update
                            .mmr_leaf
                            .as_ref()
                            .unwrap()
                            .beefy_next_authority_set
                            .unwrap()
                            .len,
                        root: H256::decode(
                            &mut &mmr_update
                                .mmr_leaf
                                .as_ref()
                                .unwrap()
                                .beefy_next_authority_set
                                .unwrap()
                                .authority_root,
                        )
                        .unwrap(),
                    },
                    parachain_heads: H256::decode(
                        &mut &mmr_update.mmr_leaf.as_ref().unwrap().parachain_heads,
                    )
                    .unwrap(),
                },
                mmr_proof: Proof {
                    leaf_index: mmr_update.mmr_leaf_index,
                    leaf_count: mmr_update.mmr_leaf_index + 1,
                    items: mmr_update
                        .mmr_proof
                        .into_iter()
                        .map(|item| H256::decode(&mut &item).unwrap())
                        .collect(),
                },
                authority_proof: mmr_update
                    .authorities_proof
                    .into_iter()
                    .map(|item| {
                        let mut dest = [0u8; 32];
                        dest.copy_from_slice(&item);
                        dest
                    })
                    .collect(),
            })
        } else {
            None
        };

        Ok(Self {
            parachain_headers,
            mmr_proofs: raw_header.mmr_proofs,
            mmr_size: raw_header.mmr_size,
            mmr_update_proof,
        })
    }
}

impl From<BeefyHeader> for RawBeefyHeader {
    fn from(beefy_header: BeefyHeader) -> Self {
        Self {
            parachain_headers: beefy_header
                .parachain_headers
                .into_iter()
                .map(
                    |para_header| ibc_proto::ibc::lightclients::beefy::v1::ParachainHeader {
                        parachain_header: para_header.parachain_header.encode(),
                        mmr_leaf_partial: Some(RawBeefyMmrLeafPartial {
                            version: {
                                let (major, minor) = para_header.partial_mmr_leaf.version.split();
                                merge_leaf_version(major, minor) as u32
                            },
                            parent_number: para_header.partial_mmr_leaf.parent_number_and_hash.0,
                            parent_hash: para_header
                                .partial_mmr_leaf
                                .parent_number_and_hash
                                .1
                                .encode(),
                            beefy_next_authority_set: Some(RawBeefyAuthoritySet {
                                id: para_header.partial_mmr_leaf.beefy_next_authority_set.id,
                                len: para_header.partial_mmr_leaf.beefy_next_authority_set.len,
                                authority_root: para_header
                                    .partial_mmr_leaf
                                    .beefy_next_authority_set
                                    .root
                                    .encode(),
                            }),
                        }),
                        para_id: para_header.para_id,
                        parachain_heads_proof: para_header
                            .parachain_heads_proof
                            .into_iter()
                            .map(|item| item.to_vec())
                            .collect(),
                        heads_leaf_index: para_header.heads_leaf_index,
                        heads_total_count: para_header.heads_total_count,
                        extrinsic_proof: para_header.extrinsic_proof,
                    },
                )
                .collect(),
            mmr_proofs: beefy_header.mmr_proofs,
            mmr_size: beefy_header.mmr_size,
            mmr_update_proof: if let Some(mmr_update) = beefy_header.mmr_update_proof {
                Some(RawMmrUpdateProof {
                    mmr_leaf: Some(RawBeefyMmrLeaf {
                        version: {
                            let (major, minor) = mmr_update.latest_mmr_leaf.version.split();
                            merge_leaf_version(major, minor) as u32
                        },
                        parent_number: mmr_update.latest_mmr_leaf.parent_number_and_hash.0,
                        parent_hash: mmr_update.latest_mmr_leaf.parent_number_and_hash.1.encode(),
                        beefy_next_authority_set: Some(RawBeefyAuthoritySet {
                            id: mmr_update.latest_mmr_leaf.beefy_next_authority_set.id,
                            len: mmr_update.latest_mmr_leaf.beefy_next_authority_set.len,
                            authority_root: mmr_update
                                .latest_mmr_leaf
                                .beefy_next_authority_set
                                .root
                                .encode(),
                        }),
                        parachain_heads: mmr_update.latest_mmr_leaf.parachain_heads.encode(),
                    }),
                    mmr_leaf_index: mmr_update.mmr_proof.leaf_index,
                    mmr_proof: mmr_update
                        .mmr_proof
                        .items
                        .into_iter()
                        .map(|item| item.encode())
                        .collect(),
                    signed_commitment: Some(RawSignedCommitment {
                        commitment: Some(RawCommitment {
                            payload: vec![PayloadItem {
                                payload_id: MMR_ROOT_ID.to_vec(),
                                payload_data: mmr_update
                                    .signed_commitment
                                    .commitment
                                    .payload
                                    .get_raw(&MMR_ROOT_ID)
                                    .unwrap()
                                    .clone(),
                            }],
                            block_numer: mmr_update.signed_commitment.commitment.block_number,
                            validator_set_id: mmr_update
                                .signed_commitment
                                .commitment
                                .validator_set_id,
                        }),
                        signatures: mmr_update
                            .signed_commitment
                            .signatures
                            .into_iter()
                            .map(|item| CommitmentSignature {
                                signature: item.signature.to_vec(),
                                authority_index: item.index,
                            })
                            .collect(),
                    }),
                    authorities_proof: mmr_update
                        .authority_proof
                        .into_iter()
                        .map(|item| item.to_vec())
                        .collect(),
                })
            } else {
                None
            },
        }
    }
}

impl Protobuf<RawBeefyHeader> for BeefyHeader {}

pub fn decode_parachain_header(raw_header: Vec<u8>) -> Result<SubstrateHeader<u32, H256>, Error> {
    SubstrateHeader::decode(&mut &*raw_header)
        .map_err(|_| Error::invalid_header("failed to decode parachain header"))
}

pub fn decode_header<B: Buf>(buf: B) -> Result<Header, Error> {
    RawBeefyHeader::decode(buf)
        .map_err(Error::decode)?
        .try_into()
}

pub fn decode_timestamp_extrinsic(header: ParachainHeader) -> Result<u64, Error> {
    let mut db = sp_trie::MemoryDB::<BlakeTwo256>::default();
    let mut root = Default::default();

    Ok(0)
}

#[cfg(test)]
pub mod test_util {}
