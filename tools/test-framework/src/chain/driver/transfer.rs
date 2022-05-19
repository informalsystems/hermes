/*!
   Methods for performing IBC token transfer on a chain.
*/

use crate::error::Error;
use crate::ibc::token::Token;
use crate::types::wallet::{Wallet, WalletAddress};

use super::ChainDriver;

pub fn local_transfer_token(
    driver: &ChainDriver,
    sender: &Wallet,
    recipient: &WalletAddress,
    token: &Token,
) -> Result<(), Error> {
    driver.exec(&[
        "--node",
        &driver.rpc_listen_address(),
        "tx",
        "bank",
        "send",
        &sender.address.0,
        &recipient.0,
        &token.to_string(),
        "--chain-id",
        driver.chain_id.as_str(),
        "--home",
        &driver.home_path,
        "--keyring-backend",
        "test",
        "--yes",
    ])?;

    Ok(())
}
