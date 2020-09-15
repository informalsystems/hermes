use crate::ics02_client::client_type::ClientType;
use tendermint::block::Height;

/// Abstract of consensus state update information
#[dyn_clonable::clonable]
pub trait Header: Clone + std::fmt::Debug {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;
}
