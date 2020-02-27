use crate::ics24_host::client::ClientId;

pub trait Msg {
    type ValidationError: std::error::Error;
    type Header: tendermint::lite::Header;

    fn route(&self) -> String;
    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;
    fn get_signers(&self) -> Vec<ClientId>;
    fn get_client_id(&self) -> ClientId;
    fn get_header(&self) -> Self::Header;
}

pub trait MsgUpdateClient
where
    Self: Msg,
{
    fn client_id(&self) -> ClientId;
    fn header(&self) -> Self::Header;
}
