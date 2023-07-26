use ibc_relayer_components::core::traits::sync::Async;
use secp256k1::PublicKey;

pub trait Solomachine: Async {
    type Error: Async;

    fn public_key(&self) -> &PublicKey;
}
