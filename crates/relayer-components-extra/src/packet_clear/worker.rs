use core::time::Duration;
use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::relay::traits::logs::logger::CanLogRelayTarget;

use async_trait::async_trait;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::packet_clear::traits::packet_clear::CanClearReceivePackets;
use crate::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};
use crate::std_prelude::*;

use super::traits::clear_interval::HasClearInterval;

#[async_trait]
pub trait CanSpawnPacketClearWorker<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
{
    fn spawn_packet_clear_worker(
        self,
        target: Target,
        src_channel_id: ChannelId<Self::SrcChain, Self::DstChain>,
        src_counterparty_port_id: PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: PortId<Self::DstChain, Self::SrcChain>,
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
        src_channel_id: ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Box<dyn TaskHandle> {
        let spawner = Target::target_chain(&self).runtime().spawner();

        spawner.spawn(async move {
            self.run_loop(&src_channel_id, &src_port_id, &dst_channel_id, &dst_port_id)
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
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
    );
}

#[async_trait]
impl<Relay, Target, Runtime> CanRunLoop<Target> for Relay
where
    Relay: CanLogRelayTarget<Target> + CanClearReceivePackets + HasClearInterval,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSleep,
{
    async fn run_loop(
        &self,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) {
        let runtime = Target::target_chain(self).runtime();
        let clear_interval = self.clear_interval().into();

        loop {
            let _ = self
                .clear_receive_packets(src_channel_id, src_port_id, dst_channel_id, dst_port_id)
                .await;
            runtime.sleep(Duration::from_secs(clear_interval)).await;
        }
    }
}
