//! ICS2 (client) context. The two traits `ClientReader` and `ClientKeeper` define the interface
//! that any host chain must implement to be able to process any `ClientMsg`. See
//! "ADR 003: IBC protocol implementation" for more details.

use alloc::boxed::Box;

use crate::ics02_client::client_consensus::ConsensusState;
use crate::ics02_client::error::{Error, ErrorDetail};
use crate::ics24_host::identifier::ClientId;
use crate::timestamp::Timestamp;
use crate::Height;

pub trait ConsensusReader {
    fn consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Box<dyn ConsensusState>, Error>;

    /// Similar to `consensus_state`, attempt to retrieve the consensus state,
    /// but return `None` if no state exists at the given height.
    fn maybe_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Error> {
        match self.consensus_state(client_id, height) {
            Ok(cs) => Ok(Some(cs)),
            Err(e) => match e.detail() {
                ErrorDetail::ConsensusStateNotFound(_) => Ok(None),
                _ => Err(e),
            },
        }
    }

    /// Search for the lowest consensus state higher than `height`.
    fn next_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Error>;

    /// Search for the highest consensus state lower than `height`.
    fn prev_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Error>;

    /// Returns the current timestamp of the local chain.
    fn host_timestamp(&self) -> Timestamp;
}
