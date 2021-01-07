use std::marker::PhantomData;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Attribute {
    key: String,
    value: String,
}

impl Attribute {
    pub fn new(key: String, value: String) -> Self {
        Self { key, value }
    }

    pub fn value(&self) -> String {
        self.value.clone()
    }

    pub fn key(&self) -> String {
        self.key.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventType {
    Message,
    Custom(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub tpe: EventType,
    pub attributes: Vec<Attribute>,
}

impl Event {
    pub fn new(tpe: EventType, attrs: Vec<(String, String)>) -> Self {
        Self {
            tpe,
            attributes: attrs
                .into_iter()
                .map(|(k, v)| Attribute::new(k, v))
                .collect(),
        }
    }

    /// Returns a vector containing the values within all attributes of this event
    pub fn attribute_values(&self) -> Vec<String> {
        self.attributes.iter().map(|a| a.value.clone()).collect()
    }
}

pub type HandlerResult<T, E> = Result<HandlerOutput<T>, E>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerOutput<T> {
    pub result: T,
    pub log: Vec<String>,
    pub events: Vec<Event>,
}

impl<T> HandlerOutput<T> {
    pub fn builder() -> HandlerOutputBuilder<T> {
        HandlerOutputBuilder::new()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HandlerOutputBuilder<T> {
    log: Vec<String>,
    events: Vec<Event>,
    marker: PhantomData<T>,
}

impl<T> HandlerOutputBuilder<T> {
    pub fn new() -> Self {
        Self {
            log: vec![],
            events: vec![],
            marker: PhantomData,
        }
    }

    pub fn with_log(mut self, log: impl Into<Vec<String>>) -> Self {
        self.log.append(&mut log.into());
        self
    }

    pub fn log(&mut self, log: impl Into<String>) {
        self.log.push(log.into());
    }

    pub fn with_events(mut self, events: impl Into<Vec<Event>>) -> Self {
        self.events.append(&mut events.into());
        self
    }

    pub fn emit(&mut self, event: impl Into<Event>) {
        self.events.push(event.into());
    }

    pub fn with_result(self, result: T) -> HandlerOutput<T> {
        HandlerOutput {
            result,
            log: self.log,
            events: self.events,
        }
    }
}
