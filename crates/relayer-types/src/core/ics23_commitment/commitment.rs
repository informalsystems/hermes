use crate::core::ics23_commitment::error::Error;
use crate::prelude::*;
use crate::proofs::ProofError;
use crate::tx_msg::encode_message;

use core::{convert::TryFrom, fmt};
use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
use serde::{Deserialize, Serialize};
use subtle_encoding::{Encoding, Hex};

use super::merkle::MerkleProof;

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct CommitmentRoot {
    #[serde(serialize_with = "crate::serializers::ser_hex_upper")]
    bytes: Vec<u8>,
}

impl fmt::Debug for CommitmentRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hex = Hex::upper_case().encode_to_string(&self.bytes).unwrap();
        f.debug_tuple("CommitmentRoot").field(&hex).finish()
    }
}

impl CommitmentRoot {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            bytes: Vec::from(bytes),
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.bytes
    }
}

impl From<Vec<u8>> for CommitmentRoot {
    fn from(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitmentPath;

#[derive(Clone, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct CommitmentProofBytes {
    #[serde(serialize_with = "crate::serializers::ser_hex_upper")]
    bytes: Vec<u8>,
}

impl fmt::Debug for CommitmentProofBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hex = Hex::upper_case().encode_to_string(&self.bytes).unwrap();
        f.debug_tuple("CommitmentProof").field(&hex).finish()
    }
}

impl TryFrom<Vec<u8>> for CommitmentProofBytes {
    type Error = ProofError;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        if bytes.is_empty() {
            Err(Self::Error::empty_proof())
        } else {
            Ok(Self { bytes })
        }
    }
}

impl From<CommitmentProofBytes> for Vec<u8> {
    fn from(p: CommitmentProofBytes) -> Vec<u8> {
        p.bytes
    }
}

impl TryFrom<RawMerkleProof> for CommitmentProofBytes {
    type Error = ProofError;

    fn try_from(proof: RawMerkleProof) -> Result<Self, Self::Error> {
        encode_message(&proof)
            .map_err(ProofError::encode)?
            .try_into()
    }
}

impl TryFrom<MerkleProof> for CommitmentProofBytes {
    type Error = ProofError;

    fn try_from(value: MerkleProof) -> Result<Self, Self::Error> {
        Self::try_from(RawMerkleProof::from(value))
    }
}

impl TryFrom<CommitmentProofBytes> for RawMerkleProof {
    type Error = Error;

    fn try_from(value: CommitmentProofBytes) -> Result<Self, Self::Error> {
        let value: Vec<u8> = value.into();
        let res: RawMerkleProof =
            prost::Message::decode(value.as_ref()).map_err(Error::invalid_raw_merkle_proof)?;
        Ok(res)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Deserialize, Default)]
pub struct CommitmentPrefix {
    bytes: Vec<u8>,
}

impl CommitmentPrefix {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.bytes
    }
}

impl TryFrom<Vec<u8>> for CommitmentPrefix {
    type Error = Error;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        if bytes.is_empty() {
            Err(Self::Error::empty_commitment_prefix())
        } else {
            Ok(Self { bytes })
        }
    }
}

impl fmt::Debug for CommitmentPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let converted = core::str::from_utf8(self.as_bytes());
        match converted {
            Ok(s) => write!(f, "{s}"),
            Err(_e) => write!(f, "<not valid UTF8: {:?}>", self.as_bytes()),
        }
    }
}

impl Serialize for CommitmentPrefix {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        format!("{self:?}").serialize(serializer)
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::prelude::*;
    use ibc_proto::ibc::core::commitment::v1::MerkleProof as RawMerkleProof;
    use ibc_proto::ics23::CommitmentProof;

    /// Returns a dummy `RawMerkleProof`, for testing only!
    pub fn get_dummy_merkle_proof() -> RawMerkleProof {
        let parsed = CommitmentProof { proof: None };
        let mproofs: Vec<CommitmentProof> = vec![parsed];
        RawMerkleProof { proofs: mproofs }
    }
}
