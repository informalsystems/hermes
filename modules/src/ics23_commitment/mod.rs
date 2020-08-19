use serde_derive::{Deserialize, Serialize};

use std::fmt;
use tendermint::merkle::proof::Proof;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommitmentRoot;
impl CommitmentRoot {
    pub fn from_bytes(_bytes: &[u8]) -> Self {
        // TODO
        CommitmentRoot {}
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommitmentPath;

pub type CommitmentProof = Proof;
/*
impl CommitmentProof {
    pub fn from_bytes(_bytes: &[u8]) -> Self {
        todo!()
    }

    pub fn validate_basic() -> Result<CommitmentProof, Error> {
        todo!()
    }
}
*/

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct CommitmentPrefix(Vec<u8>);

impl CommitmentPrefix {
    pub fn new(content: Vec<u8>) -> Self {
        Self { 0: content }
    }
}

impl fmt::Debug for CommitmentPrefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let converted = String::from_utf8(self.clone().0);
        match converted {
            Ok(s) => write!(f, "{}", s),
            Err(_e) => write!(f, "{:?}", &self.0),
        }
    }
}
