// pub async fn pay_packet_fee<Chain, Counterparty>(
//     tx_config: &MonoTagged<Chain, &TxConfig>,
//     port_id: &TaggedPortIdRef<'_, Chain, Counterparty>,
//     channel_id: &TaggedChannelIdRef<'_, Chain, Counterparty>,
//     sequence: &DualTagged<Chain, Counterparty, Sequence>,
//     payer: &MonoTagged<Chain, &Wallet>,
//     receive_fee: &TaggedTokenRef<'_, Chain>,
//     ack_fee: &TaggedTokenRef<'_, Chain>,
//     timeout_fee: &TaggedTokenRef<'_, Chain>,
// ) -> Result<(), Error> {
//     let message = build_pay_packet_fee_async_message(
//         port_id,
//         channel_id,
//         sequence,
//         &payer.address(),
//         receive_fee,
//         ack_fee,
//         timeout_fee,
//     )?;

//     simple_send_tx(tx_config.value(), &payer.value().key, vec![message]).await?;

//     Ok(())
// }
