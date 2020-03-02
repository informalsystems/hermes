use super::client_type::ClientType;
use crate::Height;

/// Abstract of consensus state update information
pub trait Header {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;
}
