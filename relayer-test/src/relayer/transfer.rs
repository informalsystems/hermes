use core::time::Duration;
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::transfer::{build_and_send_transfer_messages, Amount, TransferOptions};

use crate::error::Error;
use crate::ibc::denom::Denom;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::tagged::*;
use crate::types::wallet::WalletAddress;

pub fn tx_raw_ft_transfer<SrcChain: ChainHandle, DstChain: ChainHandle>(
    src_handle: &SrcChain,
    dst_handle: &DstChain,
    channel: &ConnectedChannel<SrcChain, DstChain>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    denom: &MonoTagged<SrcChain, &Denom>,
    amount: u64,
    timeout_height_offset: u64,
    timeout_seconds: Duration,
    number_messages: usize,
) -> Result<Vec<IbcEvent>, Error> {
    let transfer_options = TransferOptions {
        packet_src_port_id: channel.port_a.value().clone(),
        packet_src_channel_id: channel.channel_id_a.value().clone(),
        amount: Amount(amount.into()),
        denom: denom.value().0.clone(),
        receiver: Some(recipient.value().0.clone()),
        timeout_height_offset,
        timeout_seconds,
        number_msgs: number_messages,
    };

    let events = build_and_send_transfer_messages(src_handle, dst_handle, &transfer_options)?;

    Ok(events)
}
