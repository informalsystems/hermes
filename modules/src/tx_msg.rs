use tendermint::account::Id as AccountId;

pub trait Msg: Sized {
    type ValidationError: std::error::Error;

    // TODO -- clarify what is this function supposed to do & its connection to ICS26 routing mod.
    fn route(&self) -> String;

    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;

    fn get_signers(&self) -> Vec<AccountId>;
}
