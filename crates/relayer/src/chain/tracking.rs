use core::fmt::{Display, Error as FmtError, Formatter};

use ibc_proto::google::protobuf::Any;
use uuid::Uuid;

/// Identifier used to track an `EventBatch` along
/// the relaying pipeline until the corresponding
/// transactions are submitted and/or confirmed.
#[derive(Copy, Clone, Debug)]
pub enum TrackingId {
    /// Random identifier, used for tracking an event batch received over WebSocket.
    Uuid(Uuid),
    /// Static identifier, used as a placeholder for when there is no
    /// corresponding event batch, eg. when performing actions from
    /// the CLI or during packet clearing.
    Static(&'static str),
    /// Random identifier used to track latency of packet clearing.
    ClearedUuid(Uuid),
}

impl TrackingId {
    /// See [`TrackingId::Uuid`]
    pub fn new_uuid() -> Self {
        Self::Uuid(Uuid::new_v4())
    }

    /// See [`TrackingId::Static`]
    pub fn new_static(s: &'static str) -> Self {
        Self::Static(s)
    }

    pub fn new_cleared_uuid() -> Self {
        Self::ClearedUuid(Uuid::new_v4())
    }
}

impl Display for TrackingId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            TrackingId::Uuid(u) => {
                let mut s = u.to_string();
                s.truncate(8);
                s.fmt(f)
            }
            TrackingId::Static(s) => s.fmt(f),
            TrackingId::ClearedUuid(u) => {
                let mut uuid = "cleared/".to_owned();
                let mut s = u.to_string();
                s.truncate(8);
                uuid.push_str(&s);
                uuid.fmt(f)
            }
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
