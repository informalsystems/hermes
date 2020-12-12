use std::convert::TryFrom;
use std::fmt;

use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;

use crate::ics23_commitment::error::{Error, Kind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitmentRoot(pub Vec<u8>); // Todo: write constructor
impl CommitmentRoot {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            0: Vec::from(bytes),
        }
    }
}

impl From<Vec<u8>> for CommitmentRoot {
    fn from(v: Vec<u8>) -> Self {
        Self { 0: v }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CommitmentPath;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitmentProofBytes(Vec<u8>);

impl CommitmentProofBytes {
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }
}

impl From<Vec<u8>> for CommitmentProofBytes {
    fn from(v: Vec<u8>) -> Self {
        Self { 0: v }
    }
}

impl From<CommitmentProofBytes> for Vec<u8> {
    fn from(p: CommitmentProofBytes) -> Vec<u8> {
        p.0
    }
}
//
// impl From<MerkleProof> for CommitmentProofBytes {
//     fn from(proof: MerkleProof) -> Self {
//         let raw_proof: RawMerkleProof = proof.into();
//         raw_proof.into()
//     }
// }

impl From<RawMerkleProof> for CommitmentProofBytes {
    fn from(proof: RawMerkleProof) -> Self {
        let mut buf = Vec::new();
        prost::Message::encode(&proof, &mut buf).unwrap();
        buf.into()
    }
}

impl TryFrom<CommitmentProofBytes> for RawMerkleProof {
    type Error = Error;

    fn try_from(value: CommitmentProofBytes) -> Result<Self, Self::Error> {
        let value: Vec<u8> = value.into();
        let res: RawMerkleProof = prost::Message::decode(value.as_ref())
            .map_err(|e| Kind::InvalidRawMerkleProof.context(e))?;
        Ok(res)
    }
}

// TODO: decent getter or Protobuf trait implementation
#[derive(Clone, PartialEq, Eq)]
pub struct CommitmentPrefix(pub Vec<u8>);

impl CommitmentPrefix {
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }
}

impl From<Vec<u8>> for CommitmentPrefix {
    fn from(v: Vec<u8>) -> Self {
        Self { 0: v }
    }
}

impl fmt::Debug for CommitmentPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let converted = std::str::from_utf8(&self.0);
        match converted {
            Ok(s) => write!(f, "{}", s),
            Err(_e) => write!(f, "{:?}", &self.0),
        }
    }
}
