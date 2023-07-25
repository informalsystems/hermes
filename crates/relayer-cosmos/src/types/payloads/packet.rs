use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::Height;

pub struct CosmosReceivePacketPayload {
    pub packet: Packet,
    pub update_height: Height,
    pub proof_commitment: CommitmentProofBytes,
}

pub struct CosmosAckPacketPayload {
    pub packet: Packet,
    pub ack: Vec<u8>,
    pub update_height: Height,
    pub proof_acked: CommitmentProofBytes,
}

pub struct CosmosTimeoutUnorderedPacketPayload {
    pub height: Height,
    pub packet: Packet,
    pub proofs: Proofs,
}
