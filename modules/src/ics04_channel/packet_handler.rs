use super::packet::Sequence;
//use crate::ics04_channel::msgs::PacketMsg;
use crate::{
    ics02_client::height::Height,
    ics24_host::identifier::{ChannelId, PortId},
};

pub mod send_packet;

#[derive(Clone, Debug, PartialEq)]
pub enum PacketType {
    Send,
    Recv,
    Ack,
    To,
    ToClose,
}
#[derive(Clone, Debug)]
pub struct PacketResult {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub seq: Sequence,
    pub action: PacketType,
    pub receipt: Option<String>,
    pub seq_number: Sequence,
    pub timeout_height: Height,
    pub timeout_timestamp: u64,
    pub data: Vec<u8>,
}
