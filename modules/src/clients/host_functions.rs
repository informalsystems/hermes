use crate::core::ics02_client::error::Error;
use crate::prelude::*;
use sp_core::H256;
use std::marker::PhantomData;

/// This trait captures all the functions that the host chain should provide for
/// crypto operations.
pub trait HostFunctionsProvider: Clone {
    /// Keccak 256 hash function
    fn keccak_256(input: &[u8]) -> [u8; 32];

    /// Compressed Ecdsa public key recovery from a signature
    fn secp256k1_ecdsa_recover_compressed(
        signature: &[u8; 65],
        value: &[u8; 32],
    ) -> Option<Vec<u8>>;

    /// This function should verify membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_membership_trie_proof(
        root: &H256,
        proof: &[Vec<u8>],
        key: &[u8],
        value: &[u8],
    ) -> Result<(), Error>;

    /// This function should verify non membership in a trie proof using parity's sp-trie package
    /// with a BlakeTwo256 Hasher
    fn verify_non_membership_trie_proof(
        root: &H256,
        proof: &[Vec<u8>],
        key: &[u8],
    ) -> Result<(), Error>;

    /// Conduct a 256-bit Sha2 hash
    fn sha256_digest(data: &[u8]) -> [u8; 32];
}

/// This is a work around that allows us to have one super trait [`HostFunctionsProvider`]
/// that encapsulates all the needed host functions by different subsytems, and then
/// implement the needed traits through this wrapper.
pub struct HostFunctionsManager<T: HostFunctionsProvider>(PhantomData<T>);

// implementation for beefy host functions
impl<T> beefy_client::traits::HostFunctions for HostFunctionsManager<T>
where
    T: HostFunctionsProvider,
{
    fn keccak_256(input: &[u8]) -> [u8; 32] {
        T::keccak_256(input)
    }

    fn secp256k1_ecdsa_recover_compressed(
        signature: &[u8; 65],
        value: &[u8; 32],
    ) -> Option<Vec<u8>> {
        T::secp256k1_ecdsa_recover_compressed(signature, value)
    }
}
