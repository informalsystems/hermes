use prost_types::Any;

use crate::ics24_host::error::ValidationError;

pub trait Msg: Clone {
    type ValidationError: std::error::Error;
    type Raw: From<Self> + prost::Message;

    // TODO: Clarify what is this function supposed to do & its connection to ICS26 routing mod.
    fn route(&self) -> String;

    /// Unique type identifier for this message, to support encoding to/from `prost_types::Any`.
    fn type_url(&self) -> String;

    #[allow(clippy::wrong_self_convention)]
    fn to_any(self) -> Any {
        Any {
            type_url: self.type_url(),
            value: self.get_sign_bytes(),
        }
    }

    fn get_sign_bytes(self) -> Vec<u8> {
        let mut buf = Vec::new();
        let raw_msg: Self::Raw = self.into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }

    fn validate_basic(&self) -> Result<(), ValidationError> {
        Ok(())
    }
}
