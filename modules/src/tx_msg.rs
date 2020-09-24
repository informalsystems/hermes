use tendermint::account::Id as AccountId;

pub trait Msg {
    type ValidationError: std::error::Error;

    fn route(&self) -> String;

    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;

    fn get_signers(&self) -> Vec<AccountId>;
}
