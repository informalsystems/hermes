use secp256k1::PublicKey;

#[derive(Clone)]
pub struct SolomachineConsensusState {
    pub public_key: PublicKey,
    pub diversifier: String,
    pub timestamp: u64,
}
