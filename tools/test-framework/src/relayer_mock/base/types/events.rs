#[derive(Debug)]
pub struct Event {
    pub event_type: String,
}

impl Event {
    pub fn new(event_type: String) -> Self {
        Event { event_type }
    }
}

#[derive(Debug)]
pub struct WriteAcknowledgementEvent {}
