use async_trait::async_trait;

use crate::chain::types::aliases::{ChannelId, Height, PortId};
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketClearerWithTarget<Relay, Target>: Async
where
    Relay: HasRelayPacket,
    Target: ChainTarget<Relay>,
{
    async fn clear_packets_with_target(
        relay: &Relay,
        channel_id: &ChannelId<Target::TargetChain, Target::CounterpartyChain>,
        port_id: &PortId<Target::TargetChain, Target::CounterpartyChain>,
        counterparty_channel_id: &ChannelId<Target::CounterpartyChain, Target::TargetChain>,
        counterparty_port_id: &PortId<Target::CounterpartyChain, Target::TargetChain>,
        height: &Height<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}
