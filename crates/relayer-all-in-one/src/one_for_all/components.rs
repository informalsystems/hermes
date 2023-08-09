use ibc_relayer_components_extra::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;

use crate::one_for_all::impls::relay::packet_filter::FilterPacketFromOfa;

pub type PacketFilter = FilterPacketFromOfa;

pub type TwoWayAutoRelayer = ParallelTwoWayAutoRelay;
