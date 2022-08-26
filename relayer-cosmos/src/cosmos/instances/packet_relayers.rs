use ibc_relayer_framework::core::impls::packet_relayers::top::TopRelayer;
use ibc_relayer_framework::core::traits::packet_relayer::PacketRelayer;
use ibc_relayer_framework::one_for_all::traits::components::relay::OfaRelayComponents;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::relay::CosmosRelayContext;

pub fn full_packet_relayer<Relay>(
    max_retry: usize,
) -> impl PacketRelayer<OfaRelayContext<CosmosRelayContext<Relay>>>
where
    Relay: CosmosRelay,
    Relay::Components: OfaRelayComponents<CosmosRelayContext<Relay>>,
{
    TopRelayer::new(max_retry)
}
