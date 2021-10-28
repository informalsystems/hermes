use core::str::FromStr;
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::PortId;
use tracing::info;

use crate::bootstrap::pair::boostrap_chain_pair;
use crate::bootstrap::single::wait_wallet_amount;
use crate::chain::builder::ChainBuilder;
use crate::ibc::denom::derive_ibc_denom;
use crate::init::init_test;
use crate::relayer::channel::bootstrap_channel;
use crate::tagged::*;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new("gaiad", "data");

    let services = boostrap_chain_pair(&builder)?;

    let port_a = DualTagged::new(PortId::from_str("transfer")?);
    let port_b = DualTagged::new(PortId::from_str("transfer")?);

    let channel = bootstrap_channel(
        &services.side_a.foreign_client,
        &services.side_b.foreign_client,
        &port_a,
        &port_b,
    )?;

    info!("created new channel {:?}", channel);

    let denom_a = services.side_a.denom();

    let chaina_user1_balance = services
        .side_a
        .chain_driver()
        .query_balance(&services.side_a.wallets().user1().address(), &denom_a)?;

    info!("Sending IBC transfer");

    services.side_a.chain_driver().transfer_token(
        &port_a,
        &channel.channel_id_a,
        &services.side_a.wallets().user1().address(),
        &services.side_b.wallets().user1().address(),
        1000,
        &denom_a,
    )?;

    let denom_b = derive_ibc_denom(&port_b.as_ref(), &channel.channel_id_b.as_ref(), &denom_a)?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b.value().0
    );

    wait_wallet_amount(
        &services.side_a.chain_driver(),
        &services.side_a.wallets().user1(),
        chaina_user1_balance - 1000,
        &denom_a,
        20,
    )?;

    wait_wallet_amount(
        &services.side_b.chain_driver(),
        &services.side_b.wallets().user1(),
        1000,
        &denom_b.as_ref(),
        20,
    )?;

    info!(
        "successfully performed IBC transfer from chain {} to chain {}",
        services.side_a.chain_driver().value().chain_id,
        services.side_b.chain_driver().value().chain_id,
    );

    let chaina_user2_balance = services
        .side_a
        .chain_driver()
        .query_balance(&services.side_a.wallets().user2().address(), &denom_a)?;

    services.side_b.chain_driver().transfer_token(
        &port_b,
        &channel.channel_id_b,
        &services.side_b.wallets().user1().address(),
        &services.side_a.wallets().user2().address(),
        500,
        &denom_b.as_ref(),
    )?;

    wait_wallet_amount(
        &services.side_a.chain_driver(),
        &services.side_a.wallets().user2(),
        chaina_user2_balance + 500,
        &denom_a,
        20,
    )?;

    info!(
        "successfully performed reverse IBC transfer from chain {} back to chain {}",
        services.side_b.chain_driver().value().chain_id,
        services.side_a.chain_driver().value().chain_id
    );

    // std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
