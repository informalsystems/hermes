// TODO - remove when ICS message signer changes from AccountId to String

use std::convert::TryFrom;

use anomaly::{BoxError, Context};
use bech32::FromBase32;
use bech32::ToBase32;

use tendermint::account::Id as AccountId;

pub fn account_to_string(addr: AccountId) -> Result<String, BoxError> {
    Ok(bech32::encode("cosmos", addr.to_base32())
        .map_err(|e| Context::new("cannot generate bech32 account", Some(e.into())))?)
}

pub fn string_to_account(raw: String) -> Result<AccountId, BoxError> {
    let (_hrp, data) =
        bech32::decode(&raw).map_err(|e| Context::new("bad signer", Some(e.into())))?;
    let addr_bytes =
        Vec::<u8>::from_base32(&data).map_err(|e| Context::new("bad signer", Some(e.into())))?;

    Ok(AccountId::try_from(addr_bytes)
        .map_err(|e| Context::new("bad signer", Some(Box::new(e))))?)
}
