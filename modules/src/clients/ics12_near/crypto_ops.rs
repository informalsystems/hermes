use crate::clients::crypto_ops::crypto::CryptoOps;

pub struct NearCryptoOps;

impl CryptoOps for NearCryptoOps {
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
