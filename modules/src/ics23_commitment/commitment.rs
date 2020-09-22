use serde_derive::{Deserialize, Serialize};

use std::fmt;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommitmentPath;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommitmentProof(Vec<u8>);
impl CommitmentProof {
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }
}

impl From<Vec<u8>> for CommitmentProof {
    fn from(v: Vec<u8>) -> Self {
        Self { 0: v }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct CommitmentPrefix(Vec<u8>);

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
