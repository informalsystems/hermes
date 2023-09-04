use secp256k1::ecdsa::Signature;

use crate::methods::encode::public_key::PublicKey;

#[derive(Clone)]
pub struct SolomachineHeaderData {
    pub new_public_key: PublicKey,
    pub new_diversifier: String,
}

#[derive(Clone)]
pub struct SolomachineSignHeaderData {
    pub header_data: SolomachineHeaderData,
    pub sequence: u64,
    pub timestamp: u64,
    pub diversifier: String,
}

#[derive(Clone)]
pub struct SolomachineHeader {
    pub timestamp: u64,
    pub signature: Signature,
    pub header_data: SolomachineHeaderData,
}
