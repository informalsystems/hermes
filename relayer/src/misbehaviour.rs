use ibc::core::ics02_client::misbehaviour::AnyMisbehaviour;

use crate::light_client::AnyHeader;

#[derive(Clone, Debug, PartialEq)]
pub struct MisbehaviourEvidence {
    pub misbehaviour: AnyMisbehaviour,
    pub supporting_headers: Vec<AnyHeader>,
}
