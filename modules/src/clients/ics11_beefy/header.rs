use prost::Message;
use tendermint_proto::Protobuf;

use crate::clients::ics11_beefy::error::Error;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::header::AnyHeader;
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;
use beefy_client_primitives::{
    BeefyNextAuthoritySet, Hash, MmrUpdateProof, PartialMmrLeaf, SignatureWithAuthorityIndex,
    SignedCommitment,
};
use beefy_primitives::known_payload_ids::MMR_ROOT_ID;
use beefy_primitives::mmr::{MmrLeaf, MmrLeafVersion};
use beefy_primitives::{Commitment, Payload};
use bytes::Buf;
use codec::{Compact, Decode, Encode};
use ibc_proto::ibc::lightclients::beefy::v1::{
    BeefyAuthoritySet as RawBeefyAuthoritySet, BeefyMmrLeaf as RawBeefyMmrLeaf,
    BeefyMmrLeafPartial as RawBeefyMmrLeafPartial, Commitment as RawCommitment,
    CommitmentSignature, Header as RawBeefyHeader, MmrUpdateProof as RawMmrUpdateProof,
    PayloadItem, SignedCommitment as RawSignedCommitment,
};
use pallet_mmr_primitives::Proof;
use sp_core::H256;
use sp_runtime::generic::Header as SubstrateHeader;
use sp_runtime::traits::{BlakeTwo256, SaturatedConversion};

/// Beefy consensus header
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BeefyHeader {
    pub parachain_headers: Vec<ParachainHeader>, // contains the parachain headers
    pub mmr_proofs: Vec<Vec<u8>>,                // mmr proofs for these headers
    pub mmr_size: u64,                           // The latest mmr size
    pub mmr_update_proof: Option<MmrUpdateProof>, // Proof for updating the latest mmr root hash
}

impl crate::core::ics02_client::header::Header for BeefyHeader {
    fn client_type(&self) -> ClientType {
        ClientType::Beefy
    }

    fn wrap_any(self) -> AnyHeader {
        AnyHeader::Beefy(self)
    }
}

#[derive(Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode)]
pub struct ParachainHeader {
    pub parachain_header: SubstrateHeader<u32, BlakeTwo256>,
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
    pub extrinsic_proof: Vec<Vec<u8>>,
    /// this already encodes the actual extrinsic
    pub timestamp_extrinsic: Vec<u8>,
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
                let mmr_partial_leaf = raw_para_header
                    .mmr_leaf_partial
                    .ok_or_else(Error::invalid_raw_header)?;
                let parent_hash =
                    H256::decode(&mut mmr_partial_leaf.parent_hash.as_slice()).unwrap();
                let beefy_next_authority_set =
                    if let Some(next_set) = mmr_partial_leaf.beefy_next_authority_set {
                        BeefyNextAuthoritySet {
                            id: next_set.id,
                            len: next_set.len,
                            root: H256::decode(&mut next_set.authority_root.as_slice())
                                .map_err(|e| Error::invalid_mmr_update(e.to_string()))?,
                        }
                    } else {
                        Default::default()
                    };
                Ok(ParachainHeader {
                    parachain_header: decode_parachain_header(raw_para_header.parachain_header)
                        .map_err(|_| Error::invalid_raw_header())?,
                    partial_mmr_leaf: PartialMmrLeaf {
                        version: {
                            let (major, minor) =
                                split_leaf_version(mmr_partial_leaf.version.saturated_into::<u8>());
                            MmrLeafVersion::new(major, minor)
                        },
                        parent_number_and_hash: (mmr_partial_leaf.parent_number, parent_hash),
                        beefy_next_authority_set,
                    },
                    para_id: raw_para_header.para_id,
                    parachain_heads_proof: raw_para_header
                        .parachain_heads_proof
                        .into_iter()
                        .map(|item| {
                            let mut dest = [0u8; 32];
                            if item.len() != 32 {
                                return Err(Error::invalid_raw_header());
                            }
                            dest.copy_from_slice(&*item);
                            Ok(dest)
                        })
                        .collect::<Result<Vec<_>, Error>>()?,
                    heads_leaf_index: raw_para_header.heads_leaf_index,
                    heads_total_count: raw_para_header.heads_total_count,
                    extrinsic_proof: raw_para_header.extrinsic_proof,
                    timestamp_extrinsic: raw_para_header.timestamp_extrinsic,
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let mmr_update_proof = if let Some(mmr_update) = raw_header.mmr_update_proof {
            let commitment = mmr_update
                .signed_commitment
                .as_ref()
                .ok_or_else(|| {
                    Error::invalid_mmr_update("Signed commitment is missing".to_string())
                })?
                .commitment
                .as_ref()
                .ok_or_else(|| Error::invalid_mmr_update("Commitment is missing".to_string()))?;
            let payload = {
                commitment
                    .payload
                    .iter()
                    .filter_map(|item| {
                        if item.payload_id.as_slice() != MMR_ROOT_ID {
                            return None;
                        }
                        let mut payload_id = [0u8; 2];
                        payload_id.copy_from_slice(&item.payload_id);
                        Some(Payload::new(payload_id, item.payload_data.clone()))
                    })
                    .collect::<Vec<_>>()
                    .get(0)
                    .ok_or_else(|| Error::invalid_mmr_update("".to_string()))?
                    .clone()
            };
            let block_number = commitment.block_numer;
            let validator_set_id = commitment.validator_set_id;
            let signatures = mmr_update
                .signed_commitment
                .ok_or_else(|| {
                    Error::invalid_mmr_update("Signed Commiment is missing".to_string())
                })?
                .signatures
                .into_iter()
                .map(|commitment_sig| {
                    if commitment_sig.signature.len() != 65 {
                        return Err(Error::invalid_mmr_update(
                            "Invalid signature length".to_string(),
                        ));
                    }
                    Ok(SignatureWithAuthorityIndex {
                        signature: {
                            let mut sig = [0u8; 65];
                            sig.copy_from_slice(&commitment_sig.signature);
                            sig
                        },
                        index: commitment_sig.authority_index,
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?;

            let mmr_leaf = mmr_update
                .mmr_leaf
                .as_ref()
                .ok_or_else(|| Error::invalid_mmr_update("Mmr Leaf is missing".to_string()))?;
            let beefy_next_authority_set =
                mmr_leaf.beefy_next_authority_set.as_ref().ok_or_else(|| {
                    Error::invalid_mmr_update("Beefy Next Authority set is missing".to_string())
                })?;

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
                        let (major, minor) =
                            split_leaf_version(mmr_leaf.version.saturated_into::<u8>());
                        MmrLeafVersion::new(major, minor)
                    },
                    parent_number_and_hash: {
                        let parent_number = mmr_leaf.parent_number;
                        let parent_hash = H256::decode(&mut mmr_leaf.parent_hash.as_slice())
                            .map_err(|e| Error::invalid_mmr_update(e.to_string()))?;
                        (parent_number, parent_hash)
                    },
                    beefy_next_authority_set: BeefyNextAuthoritySet {
                        id: beefy_next_authority_set.id,
                        len: beefy_next_authority_set.len,
                        root: H256::decode(&mut beefy_next_authority_set.authority_root.as_slice())
                            .map_err(|e| Error::invalid_mmr_update(e.to_string()))?,
                    },
                    leaf_extra: H256::decode(&mut mmr_leaf.parachain_heads.as_slice())
                        .map_err(|e| Error::invalid_mmr_update(e.to_string()))?,
                },
                mmr_proof: Proof {
                    leaf_index: mmr_update.mmr_leaf_index,
                    leaf_count: mmr_update.mmr_leaf_index + 1,
                    items: mmr_update
                        .mmr_proof
                        .into_iter()
                        .map(|item| {
                            H256::decode(&mut &*item)
                                .map_err(|e| Error::invalid_mmr_update(e.to_string()))
                        })
                        .collect::<Result<Vec<_>, Error>>()?,
                },
                authority_proof: mmr_update
                    .authorities_proof
                    .into_iter()
                    .map(|item| {
                        if item.len() != 32 {
                            return Err(Error::invalid_mmr_update(
                                "Invalid authorities proof".to_string(),
                            ));
                        }
                        let mut dest = [0u8; 32];
                        dest.copy_from_slice(&item);
                        Ok(dest)
                    })
                    .collect::<Result<Vec<_>, Error>>()?,
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
                        timestamp_extrinsic: para_header.timestamp_extrinsic,
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
                        parachain_heads: mmr_update.latest_mmr_leaf.leaf_extra.encode(),
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

pub fn decode_parachain_header(
    raw_header: Vec<u8>,
) -> Result<SubstrateHeader<u32, BlakeTwo256>, Error> {
    SubstrateHeader::decode(&mut &*raw_header)
        .map_err(|_| Error::invalid_header("failed to decode parachain header".to_string()))
}

pub fn decode_header<B: Buf>(buf: B) -> Result<BeefyHeader, Error> {
    RawBeefyHeader::decode(buf)
        .map_err(Error::decode)?
        .try_into()
}

/// Attempt to extract the timestamp extrinsic from the parachain header
pub fn decode_timestamp_extrinsic(header: &ParachainHeader) -> Result<u64, Error> {
    let ext = &*header.timestamp_extrinsic;
    // Timestamp extrinsic should be the first inherent and hence the first extrinsic
    // https://github.com/paritytech/substrate/blob/d602397a0bbb24b5d627795b797259a44a5e29e9/primitives/trie/src/lib.rs#L99-L101
    // Decoding from the [2..] because the timestamp inmherent has two extra bytes before the call that represents the
    // call length and the extrinsic version.
    let (_, _, timestamp): (u8, u8, Compact<u64>) = codec::Decode::decode(&mut &ext[2..])
        .map_err(|_| Error::timestamp_extrinsic("Failed to decode extrinsic".to_string()))?;
    Ok(timestamp.into())
}
