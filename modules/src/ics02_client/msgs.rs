use super::client_type::ClientType;
use super::header::Header;
use super::state::ConsensusState;
use crate::ics24_host::identifier::ClientId;

// FIXME: Remove Header associated type and use Box<dyn tendermint::lite::Header> instead of
// Self::Header?

pub trait Msg {
    type ValidationError: std::error::Error;
    type Header: Header;

    fn route(&self) -> String; // TODO: Make this &'static str or custom type?
    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;
    fn get_signers(&self) -> Vec<ClientId>;
    fn get_client_id(&self) -> &ClientId;
    fn get_header(&self) -> &Self::Header;
}

pub trait MsgUpdateClient
where
    Self: Msg,
{
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
    fn header(&self) -> &Self::Header;
    fn consensus_state(&self) -> Self::ConsensusState;
}
