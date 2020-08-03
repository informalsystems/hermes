//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use crate::ics24_host::identifier::ClientId;

/// A type of message that triggers the creation of a new on-chain (IBC) client.
pub struct MsgCreateClient<C: Chain> {
    client_id: ClientId,
    client_type: C::ClientType,
    consensus_state: C::ConsensusState,
}

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
pub struct MsgUpdateClient<C: Chain> {
    client_id: ClientId,
    header: C::Header,
}
