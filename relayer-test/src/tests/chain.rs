use core::str::FromStr;
use core::time::Duration;
use eyre::{eyre, Report as Error};
use ibc::application::ics20_fungible_token_transfer::derive_ibc_denom;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::PortId;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::transfer::{build_and_send_transfer_messages, Amount, TransferOptions};
use tracing::info;

use crate::bootstrap::pair::boostrap_chain_pair;
use crate::bootstrap::single::wait_wallet_amount;
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

    let transfer_options = TransferOptions {
        packet_src_chain_config: services.config_a.clone(),
        packet_dst_chain_config: services.config_b.clone(),
        packet_src_port_id: transfer_port.clone(),
        packet_src_channel_id: channel_id_a.clone(),
        amount: Amount(1000_000.into()),
        denom: "samoleans".to_string(),
        receiver: Some(services.service_b.user.address.0.clone()),
        timeout_height_offset: 100,
        timeout_seconds: Duration::from_secs(0),
        number_msgs: 1,
    };

    info!("Sending IBC transfer");

    let res =
        build_and_send_transfer_messages(services.handle_a, services.handle_b, transfer_options)?;

    info!("IBC transfer result: {:?}", res);

    let denom_b = derive_ibc_denom(&transfer_port, &channel_id_b, "samoleans")?;

    info!(
        "Waiting for user on chain B to receive transfer in denom {}",
        denom_b
    );

    wait_wallet_amount(
        &services.service_b.chain,
        &services.service_b.user,
        1_000_000,
        &denom_b,
        20,
    )?;

    info!("successfully performed IBC transfer");

    // std::thread::sleep(Duration::from_secs(1));

    Ok(())
}
