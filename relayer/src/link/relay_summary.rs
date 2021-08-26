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
