use bech32::FromBase32;
use bech32::ToBase32;
use std::convert::TryFrom;

use tendermint::account::Id as AccountId;

pub fn account_to_string(addr: AccountId) -> Result<String, String> {
    Ok(bech32::encode("cosmos", addr.to_base32())
        .map_err(|e| "cannot generate bech32 account".to_string() + &e.to_string())?)
}

/// TODO - find a better place for this
pub fn string_to_account(raw: String) -> Result<AccountId, String> {
    let (_hrp, data) =
        bech32::decode(&raw).map_err(|e| "bad signer".to_string() + &e.to_string())?;
    let addr_bytes =
        Vec::<u8>::from_base32(&data).map_err(|e| "bad signer".to_string() + &e.to_string())?;

    Ok(AccountId::try_from(addr_bytes).map_err(|e| "bad signer".to_string() + &e.to_string())?)
}
