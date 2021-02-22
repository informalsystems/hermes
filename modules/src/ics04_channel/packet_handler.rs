use crate::{
    ics02_client::height::Height,
    ics24_host::identifier::{ChannelId, PortId},
};

use super::packet::Sequence;

pub mod send_packet;

#[derive(Clone, Debug)]
pub struct PacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub send_seq_number: Sequence,
    pub data: Vec<u8>,
    pub timeout_height: Height,
    pub timeout_timestamp: u64,
}
