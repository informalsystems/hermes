use crate::ics02_client::state::ClientState;
use crate::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::proofs::Proofs;

/// Entry point for verifying all proofs bundled in any ICS4 message.
pub fn verify_proofs(
    ctx: &dyn ChannelReader,
    channel_end: &ChannelEnd,
    connection_end: &ConnectionEnd,
    expected_chan: &ChannelEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    // This is the client which will perform proof verification.
    let client_id = connection_end.client_id().clone();

    let client_state = ctx
        .client_state(&client_id)
        .ok_or_else(|| Kind::MissingClientState(client_id.clone()))?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Kind::FrozenClient(client_id).into());
    }

    if ctx
        .client_consensus_state(&client_id, proofs.height())
        .is_none()
    {
        return Err(Kind::MissingClientConsensusState(client_id, proofs.height()).into());
    }

    let client_def = AnyClient::from_client_type(client_state.client_type());

    // Verify the proof for the channel state against the expected channel end.
    // A counterparty channel id of None in not possible, and is checked by validate_basic in msg.
    Ok(client_def
        .verify_channel_state(
            &client_state,
            proofs.height(),
            connection_end.counterparty().prefix(),
            proofs.object_proof(),
            &channel_end.counterparty().port_id(),
            &channel_end.counterparty().channel_id().unwrap(),
            expected_chan,
        )
        .map_err(|_| Kind::InvalidProof)?)
}
