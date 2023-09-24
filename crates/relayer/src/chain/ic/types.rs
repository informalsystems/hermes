use crate::chain::ic::errors::VpError;
use candid::CandidType;
use ic_cdk::export::serde::Deserialize;

#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum VecResult {
    Ok(Vec<u8>),
    Err(String),
}

impl VecResult {
    pub fn transfer_anyhow(self) -> Result<Vec<u8>, VpError> {
        match self {
            VecResult::Ok(value) => Ok(value),
            VecResult::Err(e) => Err(VpError::custom_error(e)),
        }
    }
}
