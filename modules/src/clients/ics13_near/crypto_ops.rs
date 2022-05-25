use crate::clients::{host_functions::HostFunctionsProvider, ics13_near::error::Error};

#[derive(Debug, Clone)]
pub struct NearCryptoOps {
    // _p: PhantomData<Host
}

impl HostFunctionsProvider for NearCryptoOps {
    fn keccak_256(input: &[u8]) -> [u8; 32] {
        todo!()
    }

    fn secp256k1_ecdsa_recover_compressed(signature: &[u8; 65], value: &[u8; 32]) -> Option<Vec<u8>> {
        todo!()
    }

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
}
