use crate::ics02_client::client_type::ClientType;
use crate::prelude::*;
use crate::timestamp::Timestamp;
use crate::Height;

/// Abstract of consensus state update information
pub trait Header: Clone + core::fmt::Debug + Send + Sync {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;

    /// The timestamp of the consensus state
    fn timestamp(&self) -> Timestamp;
}
