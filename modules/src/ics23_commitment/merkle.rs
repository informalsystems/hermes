use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof};

use ibc_proto::ibc::core::commitment::v1::MerklePath;

pub fn apply_prefix(
    prefix: &CommitmentPrefix,
    _path: String,
) -> Result<MerklePath, Box<dyn std::error::Error>> {
    if prefix.is_empty() {
        return Err("empty prefix".into());
    }

    // TODO
    Ok(MerklePath { key_path: None })
}

// TODO - get this from the ics23 crate proof
pub fn cosmos_specs() -> Vec<ibc_proto::ics23::ProofSpec> {
    vec![
        // Format of proofs-iavl (iavl merkle proofs)
        ibc_proto::ics23::ProofSpec {
            leaf_spec: Some(ibc_proto::ics23::LeafOp {
                hash: 1,
                prehash_key: 0,
                prehash_value: 1,
                length: 1,
                prefix: vec![0],
            }),
            inner_spec: Some(ibc_proto::ics23::InnerSpec {
                child_order: vec![0, 1],
                child_size: 33,
                min_prefix_length: 4,
                max_prefix_length: 12,
                empty_child: vec![],
                hash: 1,
            }),
            max_depth: 0,
            min_depth: 0,
        },
        // Format of proofs-tendermint (crypto/ merkle SimpleProof)
        ibc_proto::ics23::ProofSpec {
            leaf_spec: Some(ibc_proto::ics23::LeafOp {
                hash: 1,
                prehash_key: 0,
                prehash_value: 1,
                length: 1,
                prefix: vec![0],
            }),
            inner_spec: Some(ibc_proto::ics23::InnerSpec {
                child_order: vec![0, 1],
                child_size: 32,
                min_prefix_length: 1,
                max_prefix_length: 1,
                empty_child: vec![],
                hash: 1,
            }),
            max_depth: 0,
            min_depth: 0,
        },
    ]
}

use crate::ics23_commitment::error::{Error, Kind};
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
use std::convert::{TryFrom, TryInto};

#[derive(Clone, Debug, PartialEq)]
pub struct MerkleProof {
    pub proof: Option<tendermint_proto::crypto::ProofOps>,
}

impl From<MerkleProof> for Vec<u8> {
    fn from(proof: MerkleProof) -> Self {
        let mut buf = Vec::new();
        let raw_msg: RawMerkleProof = proof.into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }
}

impl TryFrom<Vec<u8>> for MerkleProof {
    type Error = Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let res: RawMerkleProof = prost::Message::decode(value.as_ref())
            .map_err(|e| Kind::InvalidRawMerkleProof.context(e))?;
        Ok(res.try_into()?)
    }
}

impl From<MerkleProof> for CommitmentProof {
    fn from(p: MerkleProof) -> Self {
        let vec: Vec<u8> = p.into();
        vec.into()
    }
}

impl TryFrom<RawMerkleProof> for MerkleProof {
    type Error = Error;
    fn try_from(value: RawMerkleProof) -> Result<Self, Self::Error> {
        Ok(MerkleProof { proof: value.proof })
    }
}

impl From<MerkleProof> for RawMerkleProof {
    fn from(value: MerkleProof) -> Self {
        RawMerkleProof { proof: value.proof }
    }
}
