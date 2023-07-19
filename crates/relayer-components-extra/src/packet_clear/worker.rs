use core::time::Duration;
use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::relay::traits::logs::logger::CanLogRelayTarget;

use async_trait::async_trait;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::packet_clear::traits::packet_clear::CanClearPackets;
use crate::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};
use crate::std_prelude::*;

#[async_trait]
pub trait CanSpawnPacketClearWorker<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
{
    fn spawn_packet_clear_worker(
        self,
        target: Target,
        channel_id: ChannelId<Self::DstChain, Self::SrcChain>,
        port_id: PortId<Self::DstChain, Self::SrcChain>,
        counterparty_channel_id: ChannelId<Self::SrcChain, Self::DstChain>,
        counterparty_port_id: PortId<Self::SrcChain, Self::DstChain>,
    ) -> Box<dyn TaskHandle>;
}

impl<Relay, Target, Runtime> CanSpawnPacketClearWorker<Target> for Relay
where
    Relay: CanRunLoop<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: HasSpawner,
{
    fn spawn_packet_clear_worker(
        self,
        _target: Target,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        counterparty_channel_id: ChannelId<Relay::SrcChain, Relay::DstChain>,
        counterparty_port_id: PortId<Relay::SrcChain, Relay::DstChain>,
    ) -> Box<dyn TaskHandle> {
        let spawner = Target::target_chain(&self).runtime().spawner();

        spawner.spawn(async move {
            self.run_loop(
                &channel_id,
                &port_id,
                &counterparty_channel_id,
                &counterparty_port_id,
            )
            .await;
        })
    }
}

#[async_trait]
trait CanRunLoop<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
{
    async fn run_loop(
        &self,
        channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        port_id: &PortId<Self::DstChain, Self::SrcChain>,
        counterparty_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        counterparty_port_id: &PortId<Self::SrcChain, Self::DstChain>,
    );
}

#[async_trait]
impl<Relay, Target, Runtime> CanRunLoop<Target> for Relay
where
    Relay: CanLogRelayTarget<Target> + CanClearPackets,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSleep,
{
    async fn run_loop(
        &self,
        channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
        counterparty_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        counterparty_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
    ) {
        let runtime = Target::target_chain(self).runtime();

        loop {
            let _ = self
                .clear_packets(
                    channel_id,
                    port_id,
                    counterparty_channel_id,
                    counterparty_port_id,
                )
                .await;
            runtime.sleep(Duration::from_secs(5)).await;
        }
    }
}
