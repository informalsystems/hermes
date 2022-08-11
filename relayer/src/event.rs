use core::fmt::{self, Display, Formatter};
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} at height {}", self.event, self.height)
    }
}

/// For use in debug messages
pub struct PrettyEvents<'a>(pub &'a [IbcEventWithHeight]);
impl<'a> Display for PrettyEvents<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "events:")?;
        for v in self.0 {
            writeln!(f, "\t{}", v)?;
        }
        Ok(())
    }
}
