use core::fmt::Display;
use ibc::{events::IbcEvent, Height};
use serde::Serialize;

pub mod bus;
pub mod monitor;
pub mod rpc;

#[derive(Clone, Debug, Serialize)]
pub struct IbcEventWithHeight {
    pub event: IbcEvent,
    pub height: Height,
}

impl IbcEventWithHeight {
    pub fn new(event: IbcEvent, height: Height) -> Self {
        Self { event, height }
    }
}

impl Display for IbcEventWithHeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at height {}", self.event, self.height)
    }
}
