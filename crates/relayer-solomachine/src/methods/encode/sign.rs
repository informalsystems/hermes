use secp256k1::ecdsa::Signature;
use secp256k1::hashes::sha256;
use secp256k1::{Message, Secp256k1, SecretKey};

/// Sign the given data by first serializing it into SHA256 digest
pub fn sign_sha256(secret_key: &SecretKey, data: &[u8]) -> Signature {
    let message = Message::from_hashed_data::<sha256::Hash>(data);

    let signature = Secp256k1::signing_only().sign_ecdsa(&message, secret_key);

    signature
}
