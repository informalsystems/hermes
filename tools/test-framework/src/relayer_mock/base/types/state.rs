use std::{collections::HashSet, fmt::Display};

#[derive(Clone, Default)]
pub struct State{
    recv_events: HashSet<String>,
    ack_events: HashSet<String>,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Received events:")?;
        for e in self.recv_events.iter() {
            writeln!(f, "\t{}", e)?;
        }
        writeln!(f, "\nAcknowledged events:")?;
        for e in self.ack_events.iter() {
            writeln!(f, "\t{}", e)?;
        }
        Ok(())
    }
}

impl State {
    pub fn check_received(
        &self,
        port_id: &String,
        channel_id: &String,
        sequence: &u128,
    ) -> bool {
        let uid = format!("{}/{}/{}", channel_id, port_id, sequence);
        self.recv_events.get(&uid).is_some()
    }

    pub fn check_acknowledged(
        &self,
        port_id: &String,
        channel_id: &String,
        sequence: &u128,
    ) -> bool {
        let uid = format!("{}/{}/{}", channel_id, port_id, sequence);
        self.ack_events.get(&uid).is_some()
    }

    pub fn update_received(&mut self, event: String) {
        self.recv_events.insert(event);
    }

    pub fn update_acknowledged(&mut self, event: String) {
        self.ack_events.insert(event);
    }
}