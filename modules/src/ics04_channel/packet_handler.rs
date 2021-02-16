pub mod send_packet;


#[derive(Clone, Debug)]
pub struct PacketResult {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
    pub channel_cap: Capability,
    pub channel_end: ChannelEnd,
}
