//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use crate::ics02_client::client_def::ClientDef;
use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;

/// A type of message that triggers the creation of a new on-chain (IBC) client.
#[derive(Clone, Debug)]
pub struct MsgCreateAnyClient<CD: ClientDef> {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub client_state: CD::ClientState,
    pub consensus_state: CD::ConsensusState,
}

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug)]
pub struct MsgUpdateAnyClient<CD: ClientDef> {
    pub client_id: ClientId,
    pub header: CD::Header,
}
