//! Domain-type definitions for requests that a
//! [`ChainHandle`] can accept. These types trickle
//! down to the [`ChainEndpoint`] trait. Any chain
//! that the ibc-relayer library supports will have
//! to implement these requests.

use ibc::core::{
    ics04_channel::channel::{Counterparty, Order},
    ics04_channel::Version,
    ics24_host::identifier::{ConnectionId, PortId},
};
use ibc_proto::ibc::core::port::v1::QueryAppVersionRequest;

/// A domain-type representation of the request
/// for fetching the version of the application
/// associated with a specific port.
#[derive(Clone, Debug)]
pub struct AppVersion {
    /// port unique identifier
    pub port_id: PortId,
    /// connection unique identifier
    pub connection_id: ConnectionId,
    /// whether the channel is ordered or unordered
    pub ordering: Order,
    /// counterparty channel end
    pub counterparty: Option<Counterparty>,
    /// proposed version
    pub proposed_version: Version,
}

/// The `AppVersion` type corresponds to the
/// proto-type gRPC [`QueryAppVersionRequest`]
/// from the IBC-go library.
///
/// Chains that do not implement the request
/// for application versions via gRPC will have
/// different proto-type representations of
/// AppVersion and therefore a separate `From`
/// implementation.
impl From<AppVersion> for QueryAppVersionRequest {
    fn from(domain: AppVersion) -> Self {
        Self {
            port_id: domain.port_id.to_string(),
            connection_id: domain.connection_id.to_string(),
            ordering: domain.ordering as i32,
            proposed_version: domain.proposed_version.to_string(),
            counterparty: domain.counterparty.map(Into::into),
        }
    }
}
