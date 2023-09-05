use crate::build::traits::components::birelay_builder::CanBuildBiRelay;
// use crate::builder::traits::birelay::HasBiRelayType;
// use crate::components::default::build::DefaultBuildComponents;
// use crate::core::traits::component::HasComponents;
// use crate::core::traits::sync::Async;

pub trait UseDefaultBuilderComponents: CanBuildBiRelay {}

// impl<Build, BaseComponents> UseDefaultBuilderComponents for Build
// where
//     Build:
//         HasBiRelayType
//         + HasComponents<Components = DefaultBuildComponents<BaseComponents>>
//         ,
//     BaseComponents: Async,
// {}
