//! This module implements the core functions of ICS02, that is, message processing logic for
//! - creating a client,
//! - updating a client, and
//! - submitting misbehavior to a client.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::msgs::MsgCreateClient;
use std::collections::HashMap;
use crate::path::{ClientStatePath, Path, ClientTypePath};
use crate::ics02_client::state::ConsensusState;

/// General processing logic for any kind of MsgCreateClient.
/// Cf. https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.
pub fn create_client(
    m: &dyn MsgCreateClient<CStateType, VErrorType>,
    private_store: HashMap<String, String>,
    mut provable_store: HashMap<String, String>,
) -> Result<(), Error>
where
    CStateType: ConsensusState,
    VErrorType: Error
{
    // Perform validation of client_id, path uniqueness, and type validation.
    // The validate_basic() method of Msg trait performs validation of client_id field.

    // Ensure no client state (for this client_id) already exists in the private store.
    let cstate_path = ClientStatePath::new(m.client_id().clone()).to_string();
    if private_store.contains_key(&cstate_path) {
        return Err(Kind::ClientAlreadyExists.context(cstate_path).into());
    }

    // Ensure no client type (for this client_id) already exists in the provable store.
    let ctype_path = ClientTypePath::new(m.client_id().clone()).to_string();
    if provable_store.contains_key(&ctype_path) {
        return Err(Kind::ClientAlreadyExists.context(ctype_path).into());
    }

    // Call into the type-specific initialization, e.g., initialise();
    todo!();

    // Finish by registering the client type in the provable store.
    provable_store.insert(ctype_path, m.client_type().as_string().into());

    Ok(())
}