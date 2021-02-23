// TODO - remove when ICS message signer changes from AccountId to String

use std::convert::TryFrom;

use anomaly::{BoxError, Context};
use bech32::ToBase32;
use bech32::{FromBase32, Variant};

use std::str::FromStr;
use tendermint::account::Id as AccountId;

pub fn encode_to_bech32(addr: String, hrp: String) -> Result<String, BoxError> {
    let account =
        AccountId::from_str(addr.as_str()).map_err(|e| Context::new("bad address", Some(e)))?;
    Ok(
        bech32::encode(hrp.as_str(), account.to_base32(), Variant::Bech32)
            .map_err(|e| Context::new("cannot generate bech32 account", Some(e.into())))?,
    )
}

pub fn string_to_account(raw: String) -> Result<AccountId, BoxError> {
    let (_hrp, data, _variant) =
        bech32::decode(&raw).map_err(|e| Context::new("bad signer", Some(e.into())))?;
    let addr_bytes =
        Vec::<u8>::from_base32(&data).map_err(|e| Context::new("bad signer", Some(e.into())))?;

    let account_id = AccountId::try_from(addr_bytes).map_err(|e| format!("bad signer: {}", e))?;
    Ok(account_id)
}
