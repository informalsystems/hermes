use ibc_relayer_types::Height;
use secp256k1::ecdsa::Signature;

pub struct SolomachineReceivePacketPayload {
    pub update_height: Height,
    pub proof_commitment: Signature,
}

pub struct SolomachineAckPacketPayload {
    pub ack: Vec<u8>,
    pub update_height: Height,
    pub proof_ack: Signature,
}

pub struct SolomachineTimeoutUnorderedPacketPayload {
    pub update_height: Height,
    pub proof_unreceived: Signature,
}
