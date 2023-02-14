use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::types::aliases::{ChainIdA, ChainIdB, ClientIdA, ClientIdB};

pub trait HasTargetChainIds: HasBiRelayType {
    fn chain_id_a(&self) -> ChainIdA<Self>;

    fn chain_id_b(&self) -> ChainIdB<Self>;
}

pub trait HasTargetClientIds: HasBiRelayType {
    fn client_id_a(&self) -> ClientIdA<Self>;

    fn client_id_b(&self) -> ClientIdB<Self>;
}
