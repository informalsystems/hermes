use strum::Display;

#[derive(Clone, Copy, Debug, Display, Eq, PartialEq)]
pub enum KeyType {
    #[strum(serialize = "secp256k1")]
    Secp256k1,
    #[strum(serialize = "ed25519")]
    Ed25519,
}
