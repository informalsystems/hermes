/*!
   Functions for performing IBC transfer that works similar to
   `hermes tx ft-transfer`.
*/

use core::ops::Add;
use core::time::Duration;
use eyre::eyre;

use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer::transfer::{build_transfer_message as raw_build_transfer_message, TransferError};
use ibc_relayer_types::applications::transfer::error::Error as Ics20Error;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::timestamp::Timestamp;

use crate::error::{handle_generic_error, Error};
use crate::ibc::denom::Denom;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;
use crate::types::wallet::{Wallet, WalletAddress};

pub fn build_transfer_message<SrcChain, DstChain>(
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    denom: &MonoTagged<SrcChain, &Denom>,
    amount: u64,
    duration: Option<Duration>,
) -> Result<Any, Error> {
    let timeout_timestamp = Timestamp::now()
        .add(duration.unwrap_or_else(|| Duration::from_secs(60)))
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
        amount.into(),
        denom.to_string(),
        sender,
        receiver,
        TimeoutHeight::no_timeout(),
        timeout_timestamp,
    ))
}

/**
   Perform a simplified version of IBC token transfer for testing purpose.

   It makes use of the local time to construct a 60 seconds IBC timeout
   for testing. During test, all chains should have the same local clock.
   We are also not really interested in setting a timeout for most tests,
   so we just put an approximate 1 minute timeout as the timeout
   field is compulsary, and we want to avoid IBC timeout on CI.

   The other reason we do not allow precise timeout to be specified is
   because it requires accessing the counterparty chain to query for
   the parameters. This will complicate the API which is unnecessary
   in most cases.

   If tests require explicit timeout, they should explicitly construct the
   transfer message and pass it to send_tx.
*/
pub async fn ibc_token_transfer<SrcChain, DstChain>(
    tx_config: &MonoTagged<SrcChain, &TxConfig>,
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    denom: &MonoTagged<SrcChain, &Denom>,
    amount: u64,
    duration: Option<Duration>,
) -> Result<Packet, Error> {
    let message = build_transfer_message(
        port_id, channel_id, sender, recipient, denom, amount, duration,
    )?;

    let events = simple_send_tx(tx_config.value(), &sender.value().key, vec![message]).await?;

    let (packet, _) = events[0]
        .iter()
        .find_map(|event| {
            if event.type_str == "send_packet" {
                extract_packet_and_write_ack_from_tx(event).ok()
            } else {
                None
            }
        })
        .ok_or_else(|| eyre!("failed to find send packet event"))?;

    Ok(packet)
}
