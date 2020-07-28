//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics

use super::client_type::ClientType;
use super::header::Header;
use super::state::ConsensusState;
use crate::ics24_host::identifier::ClientId;
// use crate::ics24_host::validate::validate_client_identifier;
use crate::ics02_client::error::{Error, Kind};
use crate::path::{ClientStatePath, ClientTypePath};
use crate::tx_msg::Msg;
use std::collections::HashMap;

/// A type of message that triggers the creation of a new on-chain (IBC) client.
pub trait MsgCreateClient
where
    Self: Msg,
{
    type ConsensusState: ConsensusState;
    type Error;

    fn client_id(&self) -> &ClientId;
    fn client_type(&self) -> ClientType;
    fn consensus_state(&self) -> Self::ConsensusState;

    fn initialise(&self) -> Result<(), Error>;

    /// General handler for processing any kind of MsgCreateClient.
    /// Cf. https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.
    fn create_client(
        &self,
        private_store: HashMap<&str, &str>,
        mut provable_store: HashMap<&str, &str>,
    ) -> Result<(), Error> {
        // Perform validation of client_id, path uniqueness, and type validation.
        // The validate_basic() method of Msg trait handles validation of client_id field.

        // Ensure no client state (for this client_id) already exists in the private store.
        let cstate_path_str: &str = &*ClientStatePath::new(self.client_id().clone()).to_string();
        if private_store.contains_key(cstate_path_str) {
            return Err(Kind::ClientAlreadyExists.context(cstate_path_str).into());
        }

        // Ensure no client type (for this client_id) already exists in the provable store.
        let ctype_path_str: &str = &*ClientTypePath::new(self.client_id().clone()).to_string();
        if provable_store.contains_key(ctype_path_str) {
            return Err(Kind::ClientAlreadyExists.context(ctype_path_str).into());
        }

        // Call into the type-specific initialization.
        todo!();

        // Finish by registering the client type in the provable store.
        provable_store.insert(ctype_path_str, self.client_type().as_string());

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
