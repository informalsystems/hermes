use core::time::Duration;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{Fee, MsgPayPacketFee, MsgRegisterCounterpartyAddress};
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use prost::{EncodeError, Message};

use crate::error::{handle_generic_error, Error};
use crate::ibc::token::TaggedTokenRef;
use crate::relayer::transfer::build_transfer_message;
use crate::relayer::tx::simple_send_tx;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::MonoTagged;
use crate::types::wallet::TaggedWallet;
use crate::types::wallet::{Wallet, WalletAddress};

pub async fn ibc_token_transfer_with_fee<SrcChain, DstChain>(
    tx_config: &MonoTagged<SrcChain, &TxConfig>,
    port_id: &TaggedPortIdRef<'_, SrcChain, DstChain>,
    channel_id: &TaggedChannelIdRef<'_, SrcChain, DstChain>,
    sender: &MonoTagged<SrcChain, &Wallet>,
    recipient: &MonoTagged<DstChain, &WalletAddress>,
    send_amount: &TaggedTokenRef<'_, SrcChain>,
    receive_fee: &TaggedTokenRef<'_, SrcChain>,
    ack_fee: &TaggedTokenRef<'_, SrcChain>,
    timeout_fee: &TaggedTokenRef<'_, SrcChain>,
    timeout: Duration,
) -> Result<(), Error> {
    let transfer_message =
        build_transfer_message(port_id, channel_id, sender, recipient, send_amount, timeout)?;

    let pay_message = build_pay_packet_message(
        port_id,
        channel_id,
        &sender.address(),
        receive_fee,
        ack_fee,
        timeout_fee,
    )?;

    let messages = vec![pay_message, transfer_message];

    simple_send_tx(tx_config.value(), &sender.value().key, messages).await?;

    Ok(())
}

pub async fn register_counterparty_address<Chain, Counterparty>(
    tx_config: &MonoTagged<Chain, &TxConfig>,
    wallet: &MonoTagged<Chain, &Wallet>,
    counterparty_address: &MonoTagged<Counterparty, &WalletAddress>,
    channel_id: &TaggedChannelIdRef<'_, Chain, Counterparty>,
) -> Result<(), Error> {
    let message = build_register_counterparty_address_message(
        &wallet.address(),
        counterparty_address,
        channel_id,
    )?;

    let messages = vec![message.into_value()];

    simple_send_tx(tx_config.value(), &wallet.value().key, messages).await?;

    Ok(())
}

fn encode_message<M: Message>(message: &M) -> Result<Vec<u8>, EncodeError> {
    let mut buf = Vec::new();
    Message::encode(message, &mut buf)?;
    Ok(buf)
}

pub fn build_pay_packet_message<Chain, Counterparty>(
    port_id: &TaggedPortIdRef<Chain, Counterparty>,
    channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
    payer: &MonoTagged<Chain, &WalletAddress>,
    receive_fee: &TaggedTokenRef<'_, Chain>,
    ack_fee: &TaggedTokenRef<'_, Chain>,
    timeout_fee: &TaggedTokenRef<'_, Chain>,
) -> Result<Any, Error> {
    const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgPayPacketFee";

    let fee = Fee {
        recv_fee: vec![Coin {
            denom: receive_fee.value().denom.to_string(),
            amount: receive_fee.value().amount.to_string(),
        }],
        ack_fee: vec![Coin {
            denom: ack_fee.value().denom.to_string(),
            amount: ack_fee.value().amount.to_string(),
        }],
        timeout_fee: vec![Coin {
            denom: timeout_fee.value().denom.to_string(),
            amount: timeout_fee.value().amount.to_string(),
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

pub fn build_register_counterparty_address_message<Chain, Counterparty>(
    address: &MonoTagged<Chain, &WalletAddress>,
    counterparty_address: &MonoTagged<Counterparty, &WalletAddress>,
    channel_id: &TaggedChannelIdRef<Chain, Counterparty>,
) -> Result<MonoTagged<Chain, Any>, Error> {
    const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgRegisterCounterpartyAddress";

    let message = MsgRegisterCounterpartyAddress {
        address: address.value().0.clone(),
        counterparty_address: counterparty_address.value().0.clone(),
        channel_id: channel_id.value().to_string(),
    };

    let encoded = encode_message(&message).map_err(handle_generic_error)?;

    let wrapped = Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    };

    Ok(MonoTagged::new(wrapped))
}
