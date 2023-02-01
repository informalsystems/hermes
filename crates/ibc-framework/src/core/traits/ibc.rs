use crate::core::traits::sync::Async;

pub trait HasIbcTypes {
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type Port: Async;

    type MerkleProof: Async;
}
