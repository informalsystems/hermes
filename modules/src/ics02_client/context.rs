use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::handler::ClientResult;
use crate::ics02_client::handler::ClientResult::{CreateResult, UpdateResult};
use crate::ics24_host::identifier::ClientId;
use tendermint::block::Height;

pub trait ClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;
    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState>;
}

pub trait ClientKeeper {
    fn store_client_result(&mut self, handler_res: ClientResult) -> Result<(), Error> {
        match handler_res {
            CreateResult(res) => {
                self.store_client_type(res.client_id.clone(), res.client_type)?;
                self.store_client_state(res.client_id.clone(), res.client_state)?;
                self.store_consensus_state(res.client_id, res.consensus_state)?;
            }
            UpdateResult(res) => {
                self.store_client_state(res.client_id.clone(), res.client_state)?;
                self.store_consensus_state(res.client_id, res.consensus_state)?;
            }
        }
        Ok(())
    }

    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Error>;

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: AnyClientState,
    ) -> Result<(), Error>;

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        consensus_state: AnyConsensusState,
    ) -> Result<(), Error>;
}
