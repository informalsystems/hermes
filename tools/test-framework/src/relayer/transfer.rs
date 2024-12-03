/*!
   Functions for performing IBC transfer that works similar to
   `hermes tx ft-transfer`.
*/

use core::ops::Add;
use core::time::Duration;
use eyre::eyre;
use ibc_relayer_types::events::IbcEvent;

use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::batched_send_tx;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::transfer::build_transfer_message as raw_build_transfer_message;
use ibc_relayer::transfer::TransferError;
use ibc_relayer_types::applications::transfer::error::Error as Ics20Error;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::timestamp::Timestamp;
use tendermint_rpc::HttpClient;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};
use crate::ibc::token::TaggedTokenRef;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;
use crate::types::wallet::{Wallet, WalletAddress};

pub fn build_transfer_message<SrcChain, DstChain>(
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    token: &TaggedTokenRef<'_, SrcChain>,
    timeout: Duration,
    memo: Option<String>,
) -> Result<Any, Error> {
    let timeout_timestamp = Timestamp::now()
        .add(timeout)
        .map_err(handle_generic_error)?;

    let sender = sender
        .value()
        .address
        .0
        .parse()
        .map_err(|e| TransferError::token_transfer(Ics20Error::signer(e)))?;

    let receiver = recipient
        .value()
        .0
        .parse()
        .map_err(|e| TransferError::token_transfer(Ics20Error::signer(e)))?;

    Ok(raw_build_transfer_message(
        (*port_id.value()).clone(),
        (*channel_id.value()).clone(),
        token.value().amount,
        token.value().denom.to_string(),
        sender,
        receiver,
        TimeoutHeight::no_timeout(),
        timeout_timestamp,
        memo,
    ))
}

/**
   Perform a simplified version of IBC token transfer for testing purpose.

   It makes use of the local time to construct a 60 seconds IBC timeout
   for testing. During test, all chains should have the same local clock.
   We are also not really interested in setting a timeout for most tests,
   so we just put an approximate 1 minute timeout as the timeout
   field is compulsory, and we want to avoid IBC timeout on CI.

   The other reason we do not allow precise timeout to be specified is
   because it requires accessing the counterparty chain to query for
   the parameters. This will complicate the API which is unnecessary
   in most cases.

   If tests require explicit timeout, they should explicitly construct the
   transfer message and pass it to send_tx.
*/
pub async fn ibc_token_transfer<SrcChain, DstChain>(
    rpc_client: MonoTagged<SrcChain, &HttpClient>,
    tx_config: &MonoTagged<SrcChain, &TxConfig>,
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    token: &TaggedTokenRef<'_, SrcChain>,
    memo: Option<String>,
    timeout: Option<Duration>,
) -> Result<(), Error> {
    let message = build_transfer_message(
        port_id,
        channel_id,
        sender,
        recipient,
        token,
        timeout.unwrap_or(Duration::from_secs(60)),
        memo.clone(),
    )?;

    let key = &sender
        .value()
        .key
        .downcast()
        .ok_or_else(|| eyre!("unable to downcast key"))
        .map_err(Error::generic)?;
    let events = simple_send_tx(
        rpc_client.into_value(),
        tx_config.value(),
        key,
        vec![message],
    )
    .await?;

    let _packet = events
        .into_iter()
        .find_map(|event| match event.event {
            IbcEvent::SendPacket(ev) => Some(ev.packet),
            _ => None,
        })
        .ok_or_else(|| eyre!("failed to find send packet event"))?;

    Ok(())
}

pub fn local_namada_token_transfer(
    home_path: &str,
    sender: &str,
    recipient: &str,
    denom: &str,
    amount: &str,
    rpc_port: &str,
) -> Result<(), Error> {
    simple_exec(
        "namada local transfer",
        "namadac",
        &[
            "--base-dir",
            home_path,
            "transparent-transfer",
            "--source",
            sender,
            "--target",
            recipient,
            "--token",
            denom,
            "--amount",
            amount,
            "--signing-keys",
            &format!("{sender}-key"),
            "--gas-limit",
            "150000",
            "--node",
            &format!("http://127.0.0.1:{rpc_port}"),
        ],
    )?;

    Ok(())
}

pub fn ibc_namada_token_transfer(
    home_path: &str,
    sender: &str,
    receiver: &str,
    denom: &str,
    amount: &str,
    channel_id: &str,
    rpc_port: &str,
    memo: Option<String>,
    timeout: Option<Duration>,
) -> Result<(), Error> {
    let signing_key = format!("{sender}-key");
    let node = format!("http://127.0.0.1:{rpc_port}");
    let mut args = vec![
        "--base-dir",
        home_path,
        "ibc-transfer",
        "--source",
        sender,
        "--receiver",
        receiver,
        "--token",
        denom,
        "--amount",
        amount,
        "--signing-keys",
        &signing_key,
        "--channel-id",
        channel_id,
        "--gas-limit",
        "150000",
        "--node",
        &node,
    ];

    let memo_str = memo.clone().unwrap_or_default();
    if memo.is_some() {
        args.push("--ibc-memo");
        args.push(&memo_str);
    }

    let timeout_str;
    if let Some(timeout) = timeout {
        args.push("--timeout-sec-offset");
        timeout_str = timeout.as_secs().to_string();
        args.push(&timeout_str);
    }

    simple_exec("namada transfer", "namadac", &args)?;

    Ok(())
}

pub async fn batched_ibc_token_transfer<SrcChain, DstChain>(
    rpc_client: MonoTagged<SrcChain, &HttpClient>,
    tx_config: &MonoTagged<SrcChain, &TxConfig>,
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    token: &TaggedTokenRef<'_, SrcChain>,
    num_msgs: usize,
    memo: Option<String>,
) -> Result<(), Error> {
    let messages = std::iter::repeat_with(|| {
        build_transfer_message(
            port_id,
            channel_id,
            sender,
            recipient,
            token,
            Duration::from_secs(60),
            memo.clone(),
        )
    })
    .take(num_msgs)
    .collect::<Result<Vec<_>, _>>()?;

    let key = &sender
        .value()
        .key
        .downcast()
        .ok_or_else(|| eyre!("unable to downcast key"))
        .map_err(Error::generic)?;
    batched_send_tx(rpc_client.value(), tx_config.value(), key, messages).await?;

    Ok(())
}
