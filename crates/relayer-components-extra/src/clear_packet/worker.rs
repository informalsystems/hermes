use async_trait::async_trait;
use core::time::Duration;

use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::clear_interval::HasClearInterval;
use ibc_relayer_components::relay::traits::components::packet_clearer::CanClearPackets;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::runtime::traits::spawn::{HasSpawner, Spawner, TaskHandle};
use crate::std_prelude::*;

#[async_trait]
pub trait CanSpawnPacketClearWorker: HasRelayChains {
    fn spawn_packet_clear_worker(
        self,
        src_channel_id: ChannelId<Self::SrcChain, Self::DstChain>,
        src_counterparty_port_id: PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: PortId<Self::DstChain, Self::SrcChain>,
    ) -> Box<dyn TaskHandle>;
}

impl<Relay> CanSpawnPacketClearWorker for Relay
where
    Relay: CanRunLoop + HasRuntime,
    Relay::Runtime: HasSpawner,
{
    fn spawn_packet_clear_worker(
        self,
        src_channel_id: ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Box<dyn TaskHandle> {
        let spawner = self.runtime().spawner();

        spawner.spawn(async move {
            self.run_loop(&src_channel_id, &src_port_id, &dst_channel_id, &dst_port_id)
                .await;
        })
    }
}

#[async_trait]
trait CanRunLoop: HasRelayChains {
    async fn run_loop(
        &self,
        src_channel_id: &ChannelId<Self::SrcChain, Self::DstChain>,
        src_port_id: &PortId<Self::SrcChain, Self::DstChain>,
        dst_channel_id: &ChannelId<Self::DstChain, Self::SrcChain>,
        dst_port_id: &PortId<Self::DstChain, Self::SrcChain>,
    );
}

#[async_trait]
impl<Relay> CanRunLoop for Relay
where
    Relay: HasRuntime + CanClearPackets + HasClearInterval,
    Relay::Runtime: CanSleep,
{
    async fn run_loop(
        &self,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) {
        let runtime = self.runtime();
        let clear_interval = self.clear_interval().into();

        loop {
            let _ = self
                .clear_packets(src_channel_id, src_port_id, dst_channel_id, dst_port_id)
                .await;
            runtime.sleep(Duration::from_secs(clear_interval)).await;
        }
    }
}
