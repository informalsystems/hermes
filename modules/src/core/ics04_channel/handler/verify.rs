use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::client_consensus::ConsensusState;
use crate::core::ics02_client::client_state::ClientState;
use crate::core::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::msgs::acknowledgement::Acknowledgement;
use crate::core::ics04_channel::packet::{Packet, Sequence};
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics26_routing::context::ReaderContext;
use crate::prelude::*;
use crate::proofs::Proofs;
use crate::Height;

/// Entry point for verifying all proofs bundled in any ICS4 message for channel protocols.
pub fn verify_channel_proofs<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    channel_end: &ChannelEnd,
    connection_end: &ConnectionEnd,
    expected_chan: &ChannelEnd,
    proof: &CommitmentProofBytes,
) -> Result<(), Error> {
    // This is the client which will perform proof verification.
    let client_id = connection_end.client_id().clone();

    let client_state = ctx.client_state(&client_id).map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(client_id));
    }

    let consensus_state = ctx
        .consensus_state(&client_id, height)
        .map_err(|_| Error::error_invalid_consensus_state())?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    // Verify the proof for the channel state against the expected channel end.
    // A counterparty channel id of None in not possible, and is checked by validate_basic in msg.
    client_def
        .verify_channel_state(
            ctx,
            &client_id,
            &client_state,
            height,
            connection_end.counterparty().prefix(),
            &proof,
            consensus_state.root(),
            channel_end.counterparty().port_id(),
            channel_end.counterparty().channel_id().unwrap(),
            expected_chan,
        )
        .map_err(Error::verify_channel_failed)
}

/// Entry point for verifying all proofs bundled in a ICS4 packet recv. message.
pub fn verify_packet_recv_proofs<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    packet: &Packet,
    connection_end: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    let client_id = connection_end.client_id();
    let client_state = ctx.client_state(client_id).map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(client_id.clone()));
    }

    let consensus_state = ctx
        .consensus_state(client_id, proofs.height())
        .map_err(|_| Error::error_invalid_consensus_state())?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    let commitment = ctx.packet_commitment(
        packet.data.clone(),
        packet.timeout_height,
        packet.timeout_timestamp,
    );

    // Verify the proof for the packet against the chain store.
    client_def
        .verify_packet_data(
            ctx,
            client_id,
            &client_state,
            height,
            connection_end,
            proofs.object_proof(),
            consensus_state.root(),
            &packet.source_port,
            &packet.source_channel,
            packet.sequence,
            commitment,
        )
        .map_err(|e| Error::packet_verification_failed(packet.sequence, e))?;

    Ok(())
}

/// Entry point for verifying all proofs bundled in an ICS4 packet ack message.
pub fn verify_packet_acknowledgement_proofs<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    packet: &Packet,
    acknowledgement: Acknowledgement,
    connection_end: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    let client_id = connection_end.client_id();
    let client_state = ctx.client_state(client_id).map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(client_id.clone()));
    }

    let consensus_state = ctx
        .consensus_state(client_id, proofs.height())
        .map_err(|_| Error::error_invalid_consensus_state())?;

    let ack_commitment = ctx.ack_commitment(acknowledgement);

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    // Verify the proof for the packet against the chain store.
    client_def
        .verify_packet_acknowledgement(
            ctx,
            client_id,
            &client_state,
            height,
            connection_end,
            proofs.object_proof(),
            consensus_state.root(),
            &packet.destination_port,
            &packet.destination_channel,
            packet.sequence,
            ack_commitment,
        )
        .map_err(|e| Error::packet_verification_failed(packet.sequence, e))?;

    Ok(())
}

/// Entry point for verifying all timeout proofs.
pub fn verify_next_sequence_recv<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
    packet: Packet,
    seq: Sequence,
    proofs: &Proofs,
) -> Result<(), Error> {
    let client_id = connection_end.client_id();
    let client_state = ctx.client_state(client_id).map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(client_id.clone()));
    }

    let consensus_state = ctx
        .consensus_state(client_id, proofs.height())
        .map_err(|_| Error::error_invalid_consensus_state())?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    // Verify the proof for the packet against the chain store.
    client_def
        .verify_next_sequence_recv(
            ctx,
            client_id,
            &client_state,
            height,
            connection_end,
            proofs.object_proof(),
            consensus_state.root(),
            &packet.destination_port,
            &packet.destination_channel,
            packet.sequence,
        )
        .map_err(|e| Error::packet_verification_failed(seq, e))?;

    Ok(())
}

pub fn verify_packet_receipt_absence<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
    packet: Packet,
    proofs: &Proofs,
) -> Result<(), Error> {
    let client_id = connection_end.client_id();
    let client_state = ctx.client_state(client_id).map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(client_id.clone()));
    }

    let consensus_state = ctx
        .consensus_state(client_id, proofs.height())
        .map_err(|_| Error::error_invalid_consensus_state())?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    // Verify the proof for the packet against the chain store.
    client_def
        .verify_packet_receipt_absence(
            ctx,
            client_id,
            &client_state,
            height,
            connection_end,
            proofs.object_proof(),
            consensus_state.root(),
            &packet.destination_port,
            &packet.destination_channel,
            packet.sequence,
        )
        .map_err(|e| Error::packet_verification_failed(packet.sequence, e))?;

    Ok(())
}
