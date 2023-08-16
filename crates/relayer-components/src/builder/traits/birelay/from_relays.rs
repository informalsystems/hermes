use async_trait::async_trait;

use crate::builder::traits::birelay::types::HasBiRelayType;
use crate::builder::types::aliases::{RelayAToB, RelayBToA};
use crate::core::traits::component::DelegateComponent;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct BiRelayFromRelayBuilderComponent;

#[async_trait]
pub trait BiRelayFromRelayBuilder<Build>
where
    Build: HasBiRelayType + HasErrorType,
{
    async fn build_birelay_from_relays(
        build: &Build,
        relay_a_to_b: RelayAToB<Build>,
        relay_b_to_a: RelayBToA<Build>,
    ) -> Result<Build::BiRelay, Build::Error>;
}

#[async_trait]
impl<Build, Component> BiRelayFromRelayBuilder<Build> for Component
where
    Build: HasBiRelayType + HasErrorType,
    Component: DelegateComponent<BiRelayFromRelayBuilderComponent>,
    Component::Delegate: BiRelayFromRelayBuilder<Build>,
{
    async fn build_birelay_from_relays(
        build: &Build,
        relay_a_to_b: RelayAToB<Build>,
        relay_b_to_a: RelayBToA<Build>,
    ) -> Result<Build::BiRelay, Build::Error> {
        Component::Delegate::build_birelay_from_relays(build, relay_a_to_b, relay_b_to_a).await
    }
}

#[async_trait]
pub trait CanBuildBiRelayFromRelays: HasBiRelayType + HasErrorType {
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: RelayAToB<Self>,
        relay_b_to_a: RelayBToA<Self>,
    ) -> Result<Self::BiRelay, Self::Error>;
}

#[async_trait]
impl<Build> CanBuildBiRelayFromRelays for Build
where
    Build: HasBiRelayType + HasErrorType + DelegateComponent<BiRelayFromRelayBuilderComponent>,
    Build::Delegate: BiRelayFromRelayBuilder<Build>,
{
    async fn build_birelay_from_relays(
        &self,
        relay_a_to_b: RelayAToB<Self>,
        relay_b_to_a: RelayBToA<Self>,
    ) -> Result<Self::BiRelay, Self::Error> {
        Build::Delegate::build_birelay_from_relays(self, relay_a_to_b, relay_b_to_a).await
    }
}
