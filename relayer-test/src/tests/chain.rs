use core::str::FromStr;
use eyre::{eyre, Report as Error};
use ibc::application::ics20_fungible_token_transfer::derive_ibc_denom;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::PortId;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use tracing::info;

use crate::bootstrap::pair::boostrap_chain_pair;
use crate::bootstrap::single::{wait_wallet_amount, INITIAL_TOKEN_AMOUNT};
use crate::chain::builder::ChainBuilder;
use crate::init::init_test;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new("gaiad", "data");

    let services = boostrap_chain_pair(&builder)?;

    let connection = Connection::new(
        services.client_a_to_b.clone(),
        services.client_b_to_a.clone(),
        default::connection_delay(),
    )?;

    let transfer_port = PortId::from_str("transfer")?;

    let channel = Channel::new(
        connection,
        Order::Unordered,
        transfer_port.clone(),
        transfer_port.clone(),
        None,
    )?;

    info!("created new channel {:?}", channel);

    let channel_id_a = channel
        .a_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?;

    let channel_id_b = channel
        .b_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?;

    let denom_a = services.service_a.denom;

    info!("Sending IBC transfer");

    services.service_a.chain.transfer_token(
        &transfer_port,
        &channel_id_a,
        &services.service_a.user1.address,
        &services.service_b.user1.address,
        1000,
        &denom_a,
    )?;

    let denom_b = derive_ibc_denom(&transfer_port, &channel_id_b, &denom_a)?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b
    );

    wait_wallet_amount(
        &services.service_a.chain,
        &services.service_a.user1,
        INITIAL_TOKEN_AMOUNT - 1000,
        &denom_a,
        20,
    )?;

    wait_wallet_amount(
        &services.service_b.chain,
        &services.service_b.user1,
        1000,
        &denom_b,
        20,
    )?;

    info!(
        "successfully performed IBC transfer from chain {} to chain {}",
        services.service_a.chain.chain_id, services.service_b.chain.chain_id
    );

    services.service_b.chain.transfer_token(
        &transfer_port,
        &channel_id_b,
        &services.service_b.user1.address,
        &services.service_a.user2.address,
        500,
        &denom_b,
    )?;

    wait_wallet_amount(
        &services.service_a.chain,
        &services.service_a.user2,
        INITIAL_TOKEN_AMOUNT + 500,
        &denom_a,
        20,
    )?;

    info!(
        "successfully performed reverse IBC transfer from chain {} back to chain {}",
        services.service_b.chain.chain_id, services.service_a.chain.chain_id
    );

    // std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
