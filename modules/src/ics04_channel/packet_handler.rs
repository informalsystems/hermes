use crate::ics24_host::identifier::{PortId,ChannelId};

use super::packet::Sequence;

pub mod send_packet;

#[derive(Clone, Debug)]
pub struct PacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub send_seq_number: Sequence,
    pub commitment: u64,
}
