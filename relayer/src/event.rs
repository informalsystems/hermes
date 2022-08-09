use core::fmt::Display;
use ibc::{events::IbcEvent, Height};

pub mod bus;
pub mod monitor;
pub mod rpc;

#[derive(Clone, Debug)]
pub struct IbcEventWithHeight {
    pub event: IbcEvent,
    pub height: Height,
}

impl IbcEventWithHeight {
    pub fn new(event: IbcEvent, height: Height) -> Self {
        Self { event, height }
    }

    pub fn event(&self) -> &IbcEvent {
        &self.event
    }

    pub fn height(&self) -> &Height {
        &self.height
    }
}

impl Display for IbcEventWithHeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at height {}", self.event, self.height)
    }
}
