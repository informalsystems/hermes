//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use super::client_type::ClientType;
use super::header::Header;
use super::state::ConsensusState;
use crate::ics24_host::identifier::ClientId;
// use crate::ics24_host::validate::validate_client_identifier;
use crate::ics02_client::error::{Error, Kind};
use crate::path::{ClientStatePath, Path};
use crate::tx_msg::Msg;
use std::collections::HashMap;

/// A type of message that triggers the creation of a new on-chain (IBC) client.
pub trait MsgCreateClient
where
    Self: Msg,
{
    type ConsensusState: ConsensusState;

    fn client_id(&self) -> &ClientId;
    fn client_type(&self) -> ClientType;
    fn consensus_state(&self) -> Self::ConsensusState;

    /// General handler for processing any kind of MsgCreateClient.
    fn create_client(
        &self,
        private_store: HashMap<&str, &str>,
        _provable_store: HashMap<&str, &str>,
    ) -> Result<(), Error> {
        // Perform validation of client_id, path uniqueness, and type validation.
        // The validate_basic() method of Msg trait handles validation of client_id field.

        let cs_path_str: &str = &*ClientStatePath::new(self.client_id().clone()).to_string();
        // let ct_path_str: &str =

        // Ensure that no client with this identifier already exists.
        if private_store.contains_key(cs_path_str) {
            return Err(Kind::ClientAlreadyExists.context(cs_path_str).into());
        }

        // abortSystemUnless(provableStore.get(clientTypePath(id)) === null)
        // clientType.initialise(consensusState)
        // provableStore.set(clientTypePath(id), clientType)

        Ok(())
    }
}

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
pub trait MsgUpdateClient
where
    Self: Msg,
{
    type Header: Header;
    fn client_id(&self) -> &ClientId;
    fn header(&self) -> &Self::Header;
}
