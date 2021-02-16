use crate::application::ics20_fungible_token_transfer::context::ICS20Context;
use crate::application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use crate::application::ics20_fungible_token_transfer::error::{Error, Kind};
use crate::ics04_channel::packet::{Packet,Sequence};
use crate::ics04_channel::packet_handler::send_packet::send_packet;
// use crate::ics04_channel::error::Error as ICS04Error;
// use crate::ics04_channel::error::Kind as ICS04Kind;


pub(crate) fn send_transfer<Ctx>(ctx: &Ctx, msg: MsgTransfer) -> Result<(), Error>
where
    Ctx: ICS20Context,
{


    let sourceChannelEnd = ctx.channel_end(&(
						msg.source_port.clone(), 
						msg.source_channel.clone()
					));
	if sourceChannelEnd.is_none() {
		return Err(Kind::ChannelNotFound(msg.source_port.clone(), msg.source_channel.clone()).into());
	}


	let destination_port = sourceChannelEnd.unwrap().counterparty().port_id().clone();
	let destination_channel =  sourceChannelEnd.unwrap().counterparty().channel_id().clone();

	if destination_channel.is_none() {
		return Err(Kind::DestinationChannelNotFound(msg.source_port.clone(), msg.source_channel.clone()).into());
	}

	// get the next sequence
	let sequence = ctx.get_next_sequence_send(&(msg.source_port.clone(), msg.source_channel.clone()));
	if sequence.is_none() {
		return Err(Kind::SequenceSendNotFound(msg.source_port,msg.source_channel).clone().into());
	}

	// begin createOutgoingPacket logic
	let channel_cap = ctx.lookup_module_by_port(&msg.source_port.clone());
	// k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(sourcePort, sourceChannel))
	if channel_cap.is_none() {
		return Err(Kind::ChannelCapabilityNotFound.into());
	}

	// // NOTE: denomination and hex hash correctness checked during msg.ValidateBasic
	// fullDenomPath := token.Denom

	// var err error

	// // deconstruct the token denomination into the denomination trace info
	// // to determine if the sender is the source chain
	// if strings.HasPrefix(token.Denom, "ibc/") {
	// 	fullDenomPath, err = k.DenomPathFromHash(ctx, token.Denom)
	// 	if err != nil {
	// 		return err
	// 	}
	// }

	// labels := []metrics.Label{
	// 	telemetry.NewLabel("destination-port", destinationPort),
	// 	telemetry.NewLabel("destination-channel", destinationChannel),
	// }

	// // NOTE: SendTransfer simply sends the denomination as it exists on its own
	// // chain inside the packet data. The receiving chain will perform denom
	// // prefixing as necessary.

	// if types.SenderChainIsSource(sourcePort, sourceChannel, fullDenomPath) {
	// 	labels = append(labels, telemetry.NewLabel("source", "true"))

	// 	// create the escrow address for the tokens
	// 	escrowAddress := types.GetEscrowAddress(sourcePort, sourceChannel)

	// 	// escrow source tokens. It fails if balance insufficient.
	// 	if err := k.bankKeeper.SendCoins(
	// 		ctx, sender, escrowAddress, sdk.NewCoins(token),
	// 	); err != nil {
	// 		return err
	// 	}

	// } else {
	// 	labels = append(labels, telemetry.NewLabel("source", "false"))

	// 	// transfer the coins to the module account and burn them
	// 	if err := k.bankKeeper.SendCoinsFromAccountToModule(
	// 		ctx, sender, types.ModuleName, sdk.NewCoins(token),
	// 	); err != nil {
	// 		return err
	// 	}

	// 	if err := k.bankKeeper.BurnCoins(
	// 		ctx, types.ModuleName, sdk.NewCoins(token),
	// 	); err != nil {
	// 		// NOTE: should not happen as the module account was
	// 		// retrieved on the step above and it has enough balace
	// 		// to burn.
	// 		panic(fmt.Sprintf("cannot burn coins after a successful send to a module account: %v", err))
	// 	}
	// }

	// packetData := types.NewFungibleTokenPacketData(
	// 	fullDenomPath, token.Amount.Uint64(), sender.String(), receiver,
	// )


	let packet =  Packet {
		sequence: <Sequence as From<u64>>::from(sequence.unwrap().clone()),
		source_port: msg.source_port, 
		source_channel:  msg.source_channel,
		destination_port,  
		destination_channel: destination_channel.unwrap().clone(),  
		data: vec![],
		timeout_height: msg.timeout_height.clone(),
		timeout_timestamp: msg.timeout_timestamp.clone(),
	};



   let handler_output = send_packet(ctx, channel_cap.unwrap().clone(), packet)
        .map_err(|e| Kind::HandlerRaisedError.context(e))?;
    
	// if err := k.channelKeeper.SendPacket(ctx, channelCap, packet); err != nil {
	// 	return err
	// }
	// ctx.store_packet_result(handler_output.result)
	// .map_err(|e| Kind::KeeperRaisedError.context(e))?;


	//do the  writting on the store  here  or give it to the handler send_transfer in the dispach ... that is in send_transfer ? 

    Ok(())
}
