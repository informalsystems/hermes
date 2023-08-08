use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::Height;

pub struct CosmosReceivePacketPayload {
    pub update_height: Height,
    pub proof_commitment: CommitmentProofBytes,
}

pub struct CosmosAckPacketPayload {
    pub ack: Vec<u8>,
    pub update_height: Height,
    pub proof_acked: CommitmentProofBytes,
}

pub struct CosmosTimeoutUnorderedPacketPayload {
    pub update_height: Height,
    pub proof_unreceived: CommitmentProofBytes,
}
