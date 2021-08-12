use ibc_proto::ibc::core::channel::v1 as proto;

use crate::tagged::DualTagged;

pub struct QueryUnreceivedAcksRequest<Chain, Counterparty>(
    pub DualTagged<Chain, Counterparty, proto::QueryUnreceivedAcksRequest>,
);

impl<Chain, Counterparty> QueryUnreceivedAcksRequest<Chain, Counterparty> {}
