use crate::events::IBCEvent;
use std::marker::PhantomData;

pub type HandlerResult<T, E> = Result<HandlerOutput<T>, E>;

#[derive(Clone, Debug)]
pub struct HandlerOutput<T> {
    pub result: T,
    pub log: Vec<String>,
    pub events: Vec<IBCEvent>,
}

impl<T> HandlerOutput<T> {
    pub fn builder() -> HandlerOutputBuilder<T> {
        HandlerOutputBuilder::new()
    }
}

#[derive(Clone, Debug, Default)]
pub struct HandlerOutputBuilder<T> {
    log: Vec<String>,
    events: Vec<IBCEvent>,
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

    pub fn with_events(mut self, mut events: Vec<IBCEvent>) -> Self {
        self.events.append(&mut events);
        self
    }

    pub fn emit(&mut self, event: IBCEvent) {
        self.events.push(event);
    }

    pub fn with_result(self, result: T) -> HandlerOutput<T> {
        HandlerOutput {
            result,
            log: self.log,
            events: self.events,
        }
    }
}
