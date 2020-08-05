use crate::ics02_client::client::ClientDef;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics24_host::identifier::ClientId;

use tendermint::lite::Height;

pub trait ClientContext<CD>
where
    CD: ClientDef,
{
    fn client_type(&self, client_id: ClientId) -> Option<ClientType>;
    fn client_state(&self, client_id: ClientId) -> Option<CD::ClientState>;
    fn consensus_state(&self, client_id: ClientId, height: Height) -> Option<CD::ConsensusState>;
}

pub trait ClientKeeper<CD: ClientDef> {
    fn store_client_type(client_type: ClientType) -> Result<(), Error>;
    fn store_client_state(client_state: CD::ClientState) -> Result<(), Error>;
    fn store_consensus_state(consensus_state: CD::ConsensusState) -> Result<(), Error>;
}
