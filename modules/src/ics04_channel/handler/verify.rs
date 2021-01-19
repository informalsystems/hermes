use crate::ics02_client::state::ClientState;
use crate::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::proofs::Proofs;

/// Entry point for verifying all proofs bundled in any ICS4 message.
pub fn verify_proofs(
    ctx: &dyn ChannelReader,
    port_id: PortId,
    channel_id: Option<ChannelId>,
    channel_end: &ChannelEnd,
    expected_chan: &ChannelEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    let connection_end = ctx.connection_state(&channel_end.connection_hops()[0].clone());
    let client = match connection_end.clone() {
        Some(c) => c.client_id().clone(),
        None => return Err(Kind::ChannelNotFound.into()),
    };

    // Fetch the client state (IBC client on the local/host chain).
    let client_state = match channel_id {
        Some(chan) => ctx.channel_client_state(Some(&(port_id, chan)), &client),
        None => ctx.channel_client_state(None, &client),
    };

    if client_state.is_none() {
        return Err(Kind::MissingClientState.context(client.to_string()).into());
    }

    let client_st = client_state.ok_or_else(|| Kind::MissingClientState)?;

    // The client must not be frozen.
    if client_st.is_frozen() {
        return Err(Kind::FrozenClient.context(client.to_string()).into());
    }

    //match channel_id {
    // Some(chan) => {
    //     if ctx
    //         .channel_client_consensus_state(
    //             Some(&(port_id, chan)),
    //             &client.clone(),
    //             proofs.height(),
    //         )
    //         .is_none()
    //     {
    //         return Err(Kind::FrozenClient.context(client.to_string()).into());
    //     }
    // }
    //None => {
    if ctx
        .channel_client_consensus_state(None, &client, proofs.height())
        .is_none()
    {
        return Err(Kind::MissingClientConsensusState
            .context(client.to_string())
            .into());
    }
    // }
    //};

    let client_def = AnyClient::from_client_type(client_st.client_type());

    // Verify the proof for the channel state against the expected channel end.
    // A counterparty channel id of None causes `unwrap()` below and indicates an internal
    // error as this is the channel id on the counterparty chain that must always be present.
    Ok(client_def
        .verify_channel_state(
            &client_st,
            proofs.height(),
            connection_end.unwrap().counterparty().prefix(),
            proofs.object_proof(),
            &channel_end.counterparty().port_id(),
            &channel_end.counterparty().channel_id().unwrap(),
            expected_chan,
        )
        .map_err(|_| Kind::InvalidProof)?)

    //Ok(())

    // // If the message includes a client state, then verify the proof for that state.
    // if let Some(expected_client_state) = client_state {
    //     verify_client_proof(
    //         ctx,
    //         connection_end,
    //         expected_client_state,
    //         proofs.height(),
    //         proofs
    //             .client_proof()
    //             .as_ref()
    //             .ok_or(Kind::NullClientProof)?,
    //     )?;
    // }

    // // If a consensus proof is attached to the message, then verify it.
    // if let Some(proof) = proofs.consensus_proof() {
    //     Ok(verify_consensus_proof(
    //         ctx,
    //         connection_end,
    //         proofs.height(),
    //         &proof,
    //     )?)
    // } else {
    //     Ok(())
    // }
}
