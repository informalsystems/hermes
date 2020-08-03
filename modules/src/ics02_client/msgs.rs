//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

pub trait MsgUpdateClient
where
    Self: Msg,
{
    type Header: Header;
    fn client_id(&self) -> &ClientId;
    fn header(&self) -> &Self::Header;
}

pub trait MsgCreateClient
where
    Self: Msg,
{
    type ConsensusState: ConsensusState;

    fn client_id(&self) -> &ClientId;
    fn client_type(&self) -> ClientType;
    fn consensus_state(&self) -> Self::ConsensusState;
}
