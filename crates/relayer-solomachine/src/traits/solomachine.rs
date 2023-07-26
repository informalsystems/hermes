use secp256k1::PublicKey;

pub trait Solomachine {
    fn public_key(&self) -> &PublicKey;
}
