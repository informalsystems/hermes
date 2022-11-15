use alloc::string::{String, ToString};
use std::{collections::HashSet, fmt::Display};

type PortId = String;
type ChannelId = String;
type Sequence = u128;

#[derive(Clone, Default, Debug)]
pub struct State {
    recv_events: HashSet<(PortId, ChannelId, Sequence)>,
    ack_events: HashSet<(PortId, ChannelId, Sequence)>,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Received events:")?;
        for e in self.recv_events.iter() {
            writeln!(f, "\t({}, {}, {})", e.0, e.1, e.2)?;
        }
        writeln!(f, "\nAcknowledged events:")?;
        for e in self.ack_events.iter() {
            writeln!(f, "\t({}, {}, {})", e.0, e.1, e.2)?;
        }
        Ok(())
    }
}

impl State {
    pub fn check_received(&self, port_id: &String, channel_id: &String, sequence: &u128) -> bool {
        self.recv_events
            .get(&(port_id.to_string(), channel_id.to_string(), *sequence))
            .is_some()
    }

    pub fn check_acknowledged(&self, port_id: String, channel_id: String, sequence: u128) -> bool {
        self.ack_events
            .get(&(port_id, channel_id, sequence))
            .is_some()
    }

    pub fn update_received(&mut self, port_id: String, channel_id: String, sequence: u128) {
        self.recv_events.insert((port_id, channel_id, sequence));
    }

    pub fn update_acknowledged(&mut self, port_id: String, channel_id: String, sequence: u128) {
        self.ack_events.insert((port_id, channel_id, sequence));
    }
}
