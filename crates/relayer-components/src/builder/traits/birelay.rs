use async_trait::async_trait;

use crate::builder::types::aliases::{
    ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::two_way::HasTwoWayRelay;
use crate::std_prelude::*;

/// Trait for types that have access to a bi-directional relayer
/// that can relay between two connected chains in both directions.
pub trait HasBiRelayType: HasErrorType {
    /// A relay context that can relay between two chains in a bi-
    /// directional fashion.
    type BiRelay: HasTwoWayRelay;

    fn birelay_error(e: <Self::BiRelay as HasErrorType>::Error) -> Self::Error;
}

#[async_trait]
pub trait CanBuildBiRelay: HasBiRelayType + HasErrorType {
    async fn build_birelay(
        &self,
        chain_id_a: &ChainIdA<Self>,
        chain_id_b: &ChainIdB<Self>,
        client_id_a: &ClientIdA<Self>,
        client_id_b: &ClientIdB<Self>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
pub trait BiRelayBuilder<Builder>
where
    Builder: HasBiRelayType + HasErrorType,
{
    async fn build_birelay(
        builder: &Builder,
        chain_id_a: &ChainIdA<Builder>,
        chain_id_b: &ChainIdB<Builder>,
        client_id_a: &ClientIdA<Builder>,
        client_id_b: &ClientIdB<Builder>,
    ) -> Result<Builder::BiRelay, Builder::Error>;
}

#[async_trait]
pub trait CanBuildBiRelayFromRelays: HasBiRelayType + HasErrorType {
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: RelayAToB<Self>,
        relay_b_to_a: RelayBToA<Self>,
    ) -> Result<Self::BiRelay, Self::Error>;
}
