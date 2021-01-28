use crate::ics24_host::error::ValidationError;
use prost_types::Any;
use tendermint::account::Id as AccountId;

pub trait Msg: Clone {
    type ValidationError: std::error::Error;

    // TODO -- clarify what is this function supposed to do & its connection to ICS26 routing mod.
    fn route(&self) -> String;

    fn get_sign_bytes<M: From<Self> + prost::Message>(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        let raw_msg: M = self.clone().into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }

    /// Unique type identifier for this message, to support encoding to/from `prost_types::Any`.
    fn type_url(&self) -> String {
        unimplemented!()
    }

    fn to_any<M: From<Self> + prost::Message>(&self) -> Any {
        Any {
            type_url: self.type_url(),
            value: self.get_sign_bytes::<M>(),
        }
    }

    fn get_signers(&self) -> Vec<AccountId>;

    fn validate_basic(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}
