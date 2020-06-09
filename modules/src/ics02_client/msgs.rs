use super::client_type::ClientType;
use super::header::Header;
use super::state::ConsensusState;
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
