use core::fmt;

use ibc_proto::google::protobuf::Any;
use uuid::Uuid;

#[derive(Copy, Clone, Debug)]
pub enum TrackingId {
    Uuid(Uuid),
    Static(&'static str),
}

impl TrackingId {
    pub fn uuid() -> Self {
        Self::Uuid(Uuid::new_v4())
    }
}

impl fmt::Display for TrackingId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrackingId::Uuid(u) => u.fmt(f),
            TrackingId::Static(s) => s.fmt(f),
        }
    }
}

/// A wrapper over a vector of proto-encoded messages
/// (`Vec<Any>`), which has an associated tracking
/// number.
///
/// A [`TrackedMsgs`] correlates with a
/// [`TrackedEvents`](crate::link::operational_data::TrackedEvents)
/// by sharing the same `tracking_id`.
#[derive(Debug, Clone)]
pub struct TrackedMsgs {
    pub msgs: Vec<Any>,
    pub tracking_id: TrackingId,
}

impl TrackedMsgs {
    pub fn new(msgs: Vec<Any>, tracking_id: TrackingId) -> Self {
        Self { msgs, tracking_id }
    }

    pub fn new_static(msgs: Vec<Any>, tracking_id: &'static str) -> Self {
        Self {
            msgs,
            tracking_id: TrackingId::Static(tracking_id),
        }
    }

    pub fn new_uuid(msgs: Vec<Any>, tracking_id: Uuid) -> Self {
        Self {
            msgs,
            tracking_id: TrackingId::Uuid(tracking_id),
        }
    }

    pub fn new_single(msg: Any, tracking_id: &'static str) -> Self {
        Self {
            msgs: vec![msg],
            tracking_id: TrackingId::Static(tracking_id),
        }
    }

    pub fn new_single_uuid(msg: Any, tracking_id: Uuid) -> Self {
        Self {
            msgs: vec![msg],
            tracking_id: TrackingId::Uuid(tracking_id),
        }
    }

    pub fn messages(&self) -> &Vec<Any> {
        &self.msgs
    }

    pub fn tracking_id(&self) -> TrackingId {
        self.tracking_id
    }
}
