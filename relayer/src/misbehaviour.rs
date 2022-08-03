use ibc::core::ics02_client::{header::AnyHeader, misbehaviour::AnyMisbehaviour};

#[derive(Clone, Debug, PartialEq)]
pub struct MisbehaviourEvidence {
    pub misbehaviour: AnyMisbehaviour,
    pub supporting_headers: Vec<AnyHeader>,
}
