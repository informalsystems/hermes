use secp256k1::ecdsa::Signature;

use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::Height;

pub struct SolomachineChannelOpenTryPayload {
    pub ordering: Ordering,
    pub connection_hops: Vec<ConnectionId>,
    pub version: Version,
    pub update_height: Height,
    pub proof_init: Signature,
}

pub struct SolomachineChannelOpenAckPayload {
    pub version: Version,
    pub update_height: Height,
    pub proof_try: Signature,
}

pub struct SolomachineChannelOpenConfirmPayload {
    pub update_height: Height,
    pub proof_ack: Signature,
}
