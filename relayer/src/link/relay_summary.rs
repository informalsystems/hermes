use core::fmt;

use ibc::events::IbcEvent;

#[derive(Clone, Debug)]
pub struct RelaySummary {
    pub events: Vec<IbcEvent>,
    // errors: todo!(),
    // timings: todo!(),
}

impl RelaySummary {
    pub fn empty() -> Self {
        Self { events: vec![] }
    }

    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    pub fn from_events(events: Vec<IbcEvent>) -> Self {
        Self { events }
    }

    pub fn extend(&mut self, other: RelaySummary) {
        self.events.extend(other.events)
    }
}

impl fmt::Display for RelaySummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RelaySummary events: ")?;
        for e in &self.events {
            write!(f, "{}; ", e)?
        }
        write!(f, "total events = {}", self.events.len())
    }
}
