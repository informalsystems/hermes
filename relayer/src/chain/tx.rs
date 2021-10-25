use core::fmt;

use prost_types::Any;

#[derive(Debug, Clone)]
pub struct TrackedMsgs {
    pub msgs: Vec<Any>,
    pub tracking_nr: String,
}

// TODO(Adi): The tracking nr should never be empty
impl TrackedMsgs {
    pub fn new(msgs: Vec<Any>) -> Self {
        Self {
            msgs,
            tracking_nr: "".into(),
        }
    }

    pub fn new_single_msg(msg: Any) -> Self {
        Self::new(vec![msg])
    }

    pub fn empty() -> Self {
        Self::new(vec![])
    }
}

impl fmt::Display for TrackedMsgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}; len={}", self.tracking_nr, self.msgs.len())
    }
}
