use prost_types::Any;

/// A wrapper over a vector of proto-encoded messages
/// (`Vec<Any>`), which has an associated tracking
/// number.
///
/// A [`TrackedMsgs`] correlates with a
/// [`TrackedEvents`](crate::link::operational_data::TrackedEvents)
/// by sharing the same `tracking_id`.
#[derive(Debug, Clone)]
pub struct TrackedMsgs {
    msgs: Vec<Any>,
    tracking_id: String,
}

impl TrackedMsgs {
    pub fn new(msgs: Vec<Any>, tid: impl Into<String>) -> Self {
        Self {
            msgs,
            tracking_id: tid.into(),
        }
    }

    pub fn new_single(msg: Any, tid: impl Into<String>) -> Self {
        Self {
            msgs: vec![msg],
            tracking_id: tid.into(),
        }
    }

    pub fn messages(&self) -> &Vec<Any> {
        &self.msgs
    }

    pub fn tracking_id(&self) -> &str {
        &self.tracking_id
    }
}

impl From<TrackedMsgs> for Vec<Any> {
    fn from(tm: TrackedMsgs) -> Vec<Any> {
        tm.msgs
    }
}
