/*!
   Methods for performing IBC token transfer on a chain.
*/

use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::types::wallet::{Wallet, WalletAddress};

use super::ChainDriver;

pub fn local_transfer_token(
    driver: &ChainDriver,
    sender: &Wallet,
    recipient: &WalletAddress,
    amount: u64,
    denom: &Denom,
) -> Result<(), Error> {
    driver.exec(&[
        "--node",
        &driver.rpc_listen_address(),
        "tx",
        "bank",
        "send",
        &sender.address.0,
        &recipient.0,
        &format!("{}{}", amount, denom),
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
