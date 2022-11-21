use alloc::string::{String, ToString};
use std::{collections::HashSet, fmt::Display};

use crate::relayer_mock::base::types::aliases::PacketUID;

#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct State {
    sent_packets: HashSet<PacketUID>,
    recv_packets: HashSet<PacketUID>,
    ack_packets: HashSet<PacketUID>,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Sent events:")?;
        for e in self.sent_packets.iter() {
            writeln!(f, "\t({}, {}, {})", e.0, e.1, e.2)?;
        }
        writeln!(f, "Received events:")?;
        for e in self.recv_packets.iter() {
            writeln!(f, "\t({}, {}, {})", e.0, e.1, e.2)?;
        }
        writeln!(f, "\nAcknowledged events:")?;
        for e in self.ack_packets.iter() {
            writeln!(f, "\t({}, {}, {})", e.0, e.1, e.2)?;
        }
        Ok(())
    }
}

impl State {
    pub fn check_sent(&self, port_id: &String, channel_id: &String, sequence: &u128) -> bool {
        self.sent_packets
            .get(&(port_id.to_string(), channel_id.to_string(), *sequence))
            .is_some()
    }

    pub fn check_received(&self, port_id: &String, channel_id: &String, sequence: &u128) -> bool {
        self.recv_packets
            .get(&(port_id.to_string(), channel_id.to_string(), *sequence))
            .is_some()
    }

    pub fn check_acknowledged(&self, port_id: String, channel_id: String, sequence: u128) -> bool {
        self.ack_packets
            .get(&(port_id, channel_id, sequence))
            .is_some()
    }

    pub fn update_sent(&mut self, port_id: String, channel_id: String, sequence: u128) {
        self.sent_packets.insert((port_id, channel_id, sequence));
    }

    pub fn update_received(&mut self, port_id: String, channel_id: String, sequence: u128) {
        self.recv_packets.insert((port_id, channel_id, sequence));
    }

    pub fn update_acknowledged(&mut self, port_id: String, channel_id: String, sequence: u128) {
        self.ack_packets.insert((port_id, channel_id, sequence));
    }
}
