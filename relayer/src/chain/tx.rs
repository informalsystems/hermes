use core::fmt;

use prost_types::Any;

#[derive(Debug, Clone)]
pub struct TrackedMsgs {
    msgs: Vec<Any>,
    tracking_id: String,
}

impl TrackedMsgs {
    pub fn new(msgs: Vec<Any>, tid: &str) -> Self {
        Self {
            msgs,
            tracking_id: tid.into(),
        }
    }

    pub fn messages(&self) -> &Vec<Any> {
        &self.msgs
    }

    pub fn new_single(msg: Any, tid: &str) -> Self {
        Self {
            msgs: vec![msg],
            tracking_id: tid.into(),
        }
    }
}

impl From<TrackedMsgs> for Vec<Any> {
    fn from(tm: TrackedMsgs) -> Vec<Any> {
        tm.msgs
    }
}

impl fmt::Display for TrackedMsgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}; len={}", self.tracking_id, self.msgs.len())
    }
}
