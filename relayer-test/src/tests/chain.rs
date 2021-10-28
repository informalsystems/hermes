use core::str::FromStr;
use eyre::Report as Error;
use ibc::applications::ics20_fungible_token_transfer::derive_ibc_denom;
use ibc::core::ics24_host::identifier::PortId;
use tracing::info;

use crate::bootstrap::pair::boostrap_chain_pair;
use crate::bootstrap::single::{wait_wallet_amount, INITIAL_TOKEN_AMOUNT};
use crate::chain::builder::ChainBuilder;
use crate::init::init_test;
use crate::relayer::channel::bootstrap_channel;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new("gaiad", "data");

    let services = boostrap_chain_pair(&builder)?;

    let transfer_port = PortId::from_str("transfer")?;

    let channel = bootstrap_channel(
        &services.side_a.foreign_client,
        &services.side_b.foreign_client,
        transfer_port.clone(),
        transfer_port.clone(),
    )?;

    info!("created new channel {:?}", channel);

    let denom_a = services.side_a.denom;

    info!("Sending IBC transfer");

    services.side_a.chain_driver.transfer_token(
        &transfer_port,
        &channel.channel_id_a,
        &services.side_a.wallets.user1().address(),
        &services.side_b.wallets.user1().address(),
        1000,
        &denom_a,
    )?;

    let denom_b = derive_ibc_denom(&transfer_port, channel.channel_id_b.value(), &denom_a)?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b
    );

    wait_wallet_amount(
        &services.side_a.chain_driver,
        &services.side_a.wallets.user1(),
        INITIAL_TOKEN_AMOUNT - 1000,
        &denom_a,
        20,
    )?;

    wait_wallet_amount(
        &services.side_b.chain_driver,
        &services.side_b.wallets.user1(),
        1000,
        &denom_b,
        20,
    )?;

    info!(
        "successfully performed IBC transfer from chain {} to chain {}",
        services.side_a.chain_driver.chain_id, services.side_b.chain_driver.chain_id
    );

    services.side_b.chain_driver.transfer_token(
        &transfer_port,
        &channel.channel_id_b,
        &services.side_b.wallets.user1().address(),
        &services.side_a.wallets.user2().address(),
        500,
        &denom_b,
    )?;

    wait_wallet_amount(
        &services.side_a.chain_driver,
        &services.side_a.wallets.user2(),
        INITIAL_TOKEN_AMOUNT + 500,
        &denom_a,
        20,
    )?;

    info!(
        "successfully performed reverse IBC transfer from chain {} back to chain {}",
        services.side_b.chain_driver.chain_id, services.side_a.chain_driver.chain_id
    );

    // std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
