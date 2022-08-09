use ibc::{events::IbcEvent, Height};

pub mod bus;
pub mod monitor;
pub mod rpc;

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
