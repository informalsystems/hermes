use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::error::Error;
use sp_core::hashing::sha2_256;

#[derive(Debug, Clone)]
pub struct NearHostFunctions;

impl HostFunctionsProvider for NearHostFunctions {
    fn verify_membership_trie_proof(
        root: &sp_core::H256,
        proof: &[Vec<u8>],
        key: &[u8],
        value: &[u8],
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_non_membership_trie_proof(
        root: &sp_core::H256,
        proof: &[Vec<u8>],
        key: &[u8],
    ) -> Result<(), Error> {
        todo!()
    }

    fn sha256_digest(data: &[u8]) -> [u8; 32] {
        sha2_256(data)
    }

    fn keccak_256(input: &[u8]) -> [u8; 32] {
        todo!()
    }

    fn secp256k1_ecdsa_recover_compressed(
        signature: &[u8; 65],
        value: &[u8; 32],
    ) -> Option<Vec<u8>> {
        todo!()
    }
}
