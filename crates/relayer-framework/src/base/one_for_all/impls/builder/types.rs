// use crate::base::builder::traits::birelay::HasBiRelayType;
// use crate::base::one_for_all::traits::builder::{OfaBuilder, OfaBuilderPreset};
// use crate::base::one_for_all::types::builder::OfaBuilderWrapper;
// use crate::base::one_for_all::types::relay::OfaRelayWrapper;
// use crate::base::relay::traits::auto_relayer::AutoRelayer;
// use crate::base::relay::types::two_way::TwoWayRelayContext;

// impl<Builder> HasBiRelayType for OfaBuilderWrapper<Builder>
// where
//     Builder: OfaBuilder,
// {
//     type BiRelay =
//         TwoWayRelayContext<
//             <Builder::Preset as OfaBuilderPreset<Builder>>::AutoRelayer,
//             OfaRelayWrapper<
//                 Builder::RelayAToB,
//             >,
//             OfaRelayWrapper<
//                 Builder::RelayBToA,
//             >,
//         >
//     ;
// }
