use std::convert::TryFrom;

use ibc_proto::ibc::core::commitment::v1::MerklePath;
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;

use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics23_commitment::error::Error;

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

#[derive(Clone, Debug, PartialEq)]
pub struct MerkleProof {
    pub proof: Option<tendermint_proto::crypto::ProofOps>,
}

// Merkle Proof serialization notes:
// "Proof" id currently defined in a number of forms and included in a number of places
// - TmProof: in tendermint-rs/src/merkle/proof.rs:Proof
// - RawProofOps: in tendermint-proto/tendermint.cyrpto.rs:ProofOps
// - RawMerkleProof: in ibc-proto/ibc.core.commitment.v1.rs:MerkleProof
//     - structure that includes a RawProofOps in its only `proof` field.
//         #[derive(Clone, PartialEq, ::prost::Message)]
//         pub struct MerkleProof {
//             #[prost(message, optional, tag="1")]
//             pub proof: ::std::option::Option<::tendermint_proto::crypto::ProofOps>,
//         }
//  - Vec<u8>: RawMerkleProof is not explicitly used but, serialized as Vec<u8>, it is
//       included in all handshake messages that require proofs (i.e. all except the two `OpenInit`),
//       and also in all queries that require proofs
//  - MerkleProof: Domain type for RawMerkleProof, currently not used and identical to RawMerkleProof.
//       This will change with verification implementation.
//  - CommitmentProof: Defined in ibc-rs as Vec<u8> and currently used in all its messages
//
// Here are a couple of flows that illustrate the different conversions:
// IBC Messages and Handlers: sink happens in the handle verification
//    Vec<u8> -> CommitmentProof -> RawMerkleProof -> MerkleProof
//
// Relayer: from the proof in the  query response to the proof being included in a message
//    TmProof -> RawProofOps => RawMerkleProof -> MerkleProof -> verify()
//      -> MerkleProof -> RawMerkleProof -> CommitmentProof -> Vec<u8>
// Note: current implementation for ^ is simplified since verification is not yet implemented:
//    TmProof -> RawProofOps => RawMerkleProof -> CommitmentProof -> Vec<u8>
//
// Implementations of (de)serializers and conversions:
//  - commitment.rs:
//      Vec<u8> <-> CommitmentProof
//      CommitmentProof <-> RawMerkleProof
//  - merkle.rs:
//      RawMerkleProof <-> MerkleProof
//  - tendermint-rs/src/merkle/proof.rs:
//      TmProof <-> RawProofOps
//  - cosmos.rs:abci_query() converts from query proof to Merkle proof:
//      RawProofOps => RawMerkleProof
//
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
