//! ICS2 (client) context. The two traits `ClientReader` and `ClientKeeper` define the interface
//! that any host chain must implement to be able to process any `ClientMsg`. See
//! "ADR 003: IBC protocol implementation" for more details.

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::handler::ClientResult::{Create, Update};
use crate::ics02_client::handler::{ClientEvent, ClientResult};
use crate::ics24_host::identifier::ClientId;
use crate::Height;

/// Defines the read-only part of ICS2 (client functions) context.
pub trait ClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState>;
}

/// Defines the write-only part of ICS2 (client functions) context.
pub trait ClientKeeper {
    fn store_client_result(
        &mut self,
        handler_res: ClientResult,
    ) -> Result<Vec<ClientEvent>, Error> {
        match handler_res {
            Create(res) => {
                let client_id = self.next_client_id();
                self.store_client_type(client_id.clone(), res.client_type)?;
                self.store_client_state(client_id.clone(), res.client_state.clone())?;
                self.store_consensus_state(
                    client_id.clone(),
                    res.client_state.latest_height(),
                    res.consensus_state,
                )?;
                Ok(vec![ClientEvent::ClientCreated(client_id)])
            }
            Update(res) => {
                self.store_client_state(res.client_id.clone(), res.client_state.clone())?;
                self.store_consensus_state(
                    res.client_id.clone(),
                    res.client_state.latest_height(),
                    res.consensus_state,
                )?;
                Ok(vec![ClientEvent::ClientUpdated(res.client_id)])
            }
        }
    }

    fn next_client_id(&mut self) -> ClientId;

    /// Called upon successful client creation
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    /// Called upon successful client creation and update
    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: AnyClientState,
    ) -> Result<(), Error>;

    /// Called upon successful client creation and update
    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        height: Height,
        consensus_state: AnyConsensusState,
    ) -> Result<(), Error>;
}
