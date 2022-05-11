use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{Fee, MsgPayPacketFee};
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use prost::{EncodeError, Message};

use crate::error::{handle_generic_error, Error};
use crate::ibc::denom::Denom;
use crate::relayer::transfer::build_transfer_message;
use crate::relayer::tx::simple_send_tx;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::MonoTagged;
use crate::types::wallet::TaggedWallet;
use crate::types::wallet::{Wallet, WalletAddress};

fn encode_message<M: Message>(message: &M) -> Result<Vec<u8>, EncodeError> {
    let mut buf = Vec::new();
    Message::encode(message, &mut buf)?;
    Ok(buf)
}

pub fn build_pay_packet_message<Chain, Counterparty>(
    port_id: &TaggedPortIdRef<Chain, Counterparty>,
    channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
    payer: &MonoTagged<Chain, &WalletAddress>,
    denom: &MonoTagged<Chain, &Denom>,
    receive_fee: u64,
    ack_fee: u64,
    timeout_fee: u64,
) -> Result<Any, Error> {
    const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgPayPacketFee";

    let denom_str = denom.value().to_string();

    let fee = Fee {
        recv_fee: vec![Coin {
            denom: denom_str.clone(),
            amount: receive_fee.to_string(),
        }],
        ack_fee: vec![Coin {
            denom: denom_str.clone(),
            amount: ack_fee.to_string(),
        }],
        timeout_fee: vec![Coin {
            denom: denom_str,
            amount: timeout_fee.to_string(),
        }],
    };

    let message = MsgPayPacketFee {
        fee: Some(fee),
        source_port_id: port_id.value().to_string(),
        source_channel_id: channel_id.value().to_string(),
        signer: payer.value().0.clone(),
        relayers: Vec::new(),
    };

    let encoded = encode_message(&message).map_err(handle_generic_error)?;

    Ok(Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    })
}

pub async fn ibc_token_transfer_with_fee<SrcChain, DstChain>(
    tx_config: &MonoTagged<SrcChain, &TxConfig>,
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    denom: &MonoTagged<SrcChain, &Denom>,
    send_amount: u64,
    receive_fee: u64,
    ack_fee: u64,
    timeout_fee: u64,
) -> Result<(), Error> {
    let transfer_message =
        build_transfer_message(port_id, channel_id, sender, recipient, denom, send_amount)?;

    let pay_message = build_pay_packet_message(
        port_id,
        channel_id,
        &sender.address(),
        denom,
        receive_fee,
        ack_fee,
        timeout_fee,
    )?;

    let messages = vec![pay_message, transfer_message];

    simple_send_tx(tx_config.value(), &sender.value().key, messages).await?;

    Ok(())
}
