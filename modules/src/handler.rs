#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Attribute {
    key: String,
    value: String,
}

impl Attribute {
    fn new(key: String, value: String) -> Self {
        Self { key, value }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventType {
    Message,
    Custom(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    tpe: EventType,
    attributes: Vec<Attribute>,
}

impl Event {
    fn new(tpe: EventType, attrs: Vec<(String, String)>) -> Self {
        Self {
            tpe,
            attributes: attrs
                .into_iter()
                .map(|(k, v)| Attribute::new(k, v))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerOutput<T> {
    result: T,
    log: Vec<String>,
    events: Vec<Event>,
}

impl<T> HandlerOutput<T> {
    fn new(result: T) -> Self {
        Self {
            result,
            log: vec![],
            events: vec![],
        }
    }

    fn log(&mut self, log: String) {
        self.log.push(log);
    }

    fn emit(&mut self, event: impl Into<Event>) {
        self.events.push(event.into());
    }
}
