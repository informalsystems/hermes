use crate::core::ics02_client::error::Error;
use crate::prelude::*;
use beefy_client::traits::HostFunctions;
use sp_core::H256;

pub trait CryptoOps: HostFunctions + Clone {
    /// This function should verify membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_membership_trie_proof(
        root: &H256,
        proof: &Vec<Vec<u8>>,
        key: &[u8],
        value: &[u8],
    ) -> Result<(), Error>;
    /// This function should verify non membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_non_membership_trie_proof(
        root: &H256,
        proof: &Vec<Vec<u8>>,
        key: &[u8],
    ) -> Result<(), Error>;
}
