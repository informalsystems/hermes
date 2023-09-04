use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::Height;

#[derive(Debug)]
pub struct CosmosChannelOpenTryPayload {
    pub ordering: Ordering,
    pub connection_hops: Vec<ConnectionId>,
    pub version: Version,
    pub update_height: Height,
    pub proof_init: CommitmentProofBytes,
}

#[derive(Debug)]
pub struct CosmosChannelOpenAckPayload {
    pub version: Version,
    pub update_height: Height,
    pub proof_try: CommitmentProofBytes,
}

#[derive(Debug)]
pub struct CosmosChannelOpenConfirmPayload {
    pub update_height: Height,
    pub proof_ack: CommitmentProofBytes,
}
