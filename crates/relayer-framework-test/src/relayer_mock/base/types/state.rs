use std::{collections::HashMap, fmt::Display};

use crate::relayer_mock::base::types::aliases::PacketUID;
use crate::relayer_mock::base::types::height::Height;
use crate::relayer_mock::base::types::packet::PacketKey;

use super::aliases::MockTimestamp;

/// A snapshot of the mock chain's state at a point in time.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct State {
    /// The packets that the mock chain has sent.
    sent_packets: HashMap<PacketUID, (PacketKey, Height)>,
    /// The packets that the mock chain has received.
    recv_packets: HashMap<PacketUID, (PacketKey, Height)>,
    /// The ack_packets that the mock chain has received.
    ack_packets: HashMap<PacketUID, (PacketKey, Height)>,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Sent packets:")?;
        for key in self.sent_packets.keys() {
            let packet = self
                .sent_packets
                .get(key)
                .expect("error retrieving packet and height from sent_packets");
            writeln!(
                f,
                "\tPacket({}, {}, {}) with sequence {} and height {}",
                key.0, key.1, key.2, packet.0.sequence, packet.1
            )?;
        }
        writeln!(f, "Received packets:")?;
        for key in self.recv_packets.keys() {
            let packet = self
                .recv_packets
                .get(key)
                .expect("error retrieving packet and height from recv_packets");
            writeln!(
                f,
                "\tPacket({}, {}, {}) with sequence {} and height {}",
                key.0, key.1, key.2, packet.0.sequence, packet.1
            )?;
        }
        writeln!(f, "Acknowledged packets:")?;
        for key in self.ack_packets.keys() {
            let packet = self
                .ack_packets
                .get(key)
                .expect("error retrieving packet and height from ack_packets");
            writeln!(
                f,
                "\tPacket({}, {}, {}) with sequence {} and height {}",
                key.0, key.1, key.2, packet.0.sequence, packet.1
            )?;
        }
        Ok(())
    }
}

impl State {
    pub fn check_sent(&self, packet_uid: PacketUID) -> bool {
        self.sent_packets.get(&packet_uid).is_some()
    }

    pub fn check_received(&self, packet_uid: PacketUID) -> bool {
        self.recv_packets.get(&packet_uid).is_some()
    }

    pub fn check_acknowledged(&self, packet_uid: PacketUID) -> bool {
        self.ack_packets.get(&packet_uid).is_some()
    }

    /// Checks that the given packet has timed out by comparing whether
    /// the packet's timeout timestamp has exceeded the chain's current
    /// timestamp or the packet's timeout height has exceeded the chain's
    /// height.
    pub fn check_timeout(
        &self,
        packet: PacketKey,
        current_height: Height,
        current_timestamp: MockTimestamp,
    ) -> bool {
        // A packet has not timed out if its timeout height has not exceeded the chain's
        // height AND its timeout timestamp has not exceeded the chain's timestamp.
        if current_height <= packet.timeout_height && current_timestamp <= packet.timeout_timestamp
        {
            return false;
        }

        // also check that the packet has not been previously received
        !self.check_received((
            packet.dst_port_id.clone(),
            packet.dst_channel_id.clone(),
            packet.sequence,
        ))
    }

    pub fn update_sent(&mut self, packet_uid: PacketUID, packet: PacketKey, height: Height) {
        self.sent_packets.insert(packet_uid, (packet, height));
    }

    pub fn update_received(&mut self, packet_uid: PacketUID, packet: PacketKey, height: Height) {
        self.recv_packets.insert(packet_uid, (packet, height));
    }

    pub fn update_acknowledged(
        &mut self,
        packet_uid: PacketUID,
        packet: PacketKey,
        height: Height,
    ) {
        self.ack_packets.insert(packet_uid, (packet, height));
    }

    pub fn get_received(&self, packet_uid: PacketUID) -> Option<&(PacketKey, Height)> {
        self.recv_packets.get(&packet_uid)
    }
}
