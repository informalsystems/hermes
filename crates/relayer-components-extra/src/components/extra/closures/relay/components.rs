use crate::components::extra::closures::relay::auto_relayer::UseExtraAutoRelayer;
use crate::components::extra::closures::relay::event_relayer::UseExtraEventRelayer;
use crate::components::extra::closures::relay::packet_relayer::UseExtraPacketRelayer;

pub trait CanUseExtraRelayComponents:
    UseExtraPacketRelayer + UseExtraEventRelayer + UseExtraAutoRelayer
{
}
