//! This module implements the core protocol of ICS03, that is, the ICS3 connection open handshake.
//!
//! TODO: in its current state, this module is not compiled nor included in the module tree.

use crate::events::IBCEvent;
use crate::events::IBCEvent::{
    OpenAckConnection, OpenConfirmConnection, OpenInitConnection, OpenTryConnection,
};
use crate::ics03_connection::connection::{ConnectionEnd, Counterparty};
use crate::ics03_connection::ctx::ICS3Context;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics03_connection::exported::{get_compatible_versions, pick_version, State};
use crate::ics03_connection::msgs::{
    ICS3Msg, MsgConnectionOpenAck, MsgConnectionOpenConfirm, MsgConnectionOpenInit,
    MsgConnectionOpenTry,
};
use crate::proofs::Proofs;
use crate::Height;

// The outcome after delivering a specific ICS3 message.
type DeliveryOutcome = ConnectionEnd;

#[derive(Debug, Clone, Default)]
pub struct ProtocolOutput {
    object: Option<ConnectionEnd>,
    events: Vec<IBCEvent>,
}

impl ProtocolOutput {
    pub fn new() -> ProtocolOutput {
        ProtocolOutput::default()
    }

    pub fn set_object(self, ce: ConnectionEnd) -> ProtocolOutput {
        ProtocolOutput {
            object: Some(ce),
            events: self.events,
        }
    }

    pub fn add_events(self, events: &mut Vec<IBCEvent>) -> ProtocolOutput {
        let mut evs = self.events.clone();
        evs.append(events);

        ProtocolOutput {
            events: evs,
            ..self
        }
    }
}

type ProtocolResult = Result<ProtocolOutput, Error>;

/// General entry point for delivering (i.e., processing) any type of message related to the ICS03
/// connection open handshake protocol.
pub fn deliver_ics3_msg(ctx: &ICS3Context, message: &ICS3Msg) -> ProtocolResult {
    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the output consists of a ConnectionEnd.
    let object = match message {
        ICS3Msg::ConnectionOpenInit(msg) => deliver_init_msg(ctx, msg),
        ICS3Msg::ConnectionOpenTry(msg) => deliver_try_msg(ctx, msg),
        ICS3Msg::ConnectionOpenAck(msg) => deliver_ack_msg(ctx, msg),
        ICS3Msg::ConnectionOpenConfirm(msg) => deliver_confirm_msg(ctx, msg),
    }?;

    // Post-processing: emit events.
    let mut events = produce_events(ctx, message);

    Ok(ProtocolOutput::new()
        .set_object(object)
        .add_events(&mut events))
}

/// Processing logic specific to messages of type `MsgConnectionOpenInit`.
fn deliver_init_msg(
    ctx: &ICS3Context,
    msg: &MsgConnectionOpenInit,
) -> Result<DeliveryOutcome, Error> {
    // No connection should exist.
    if ctx.current_connection().is_some() {
        Err(Kind::ConnectionExistsAlready
            .context(msg.connection_id().to_string())
            .into())
    } else {
        let mut new_connection_end = ConnectionEnd::new(
            msg.client_id().clone(),
            msg.counterparty().clone(),
            get_compatible_versions(),
        )?;
        new_connection_end.set_state(State::Init);

        Ok(new_connection_end)
    }
}

fn deliver_try_msg(
    ctx: &ICS3Context,
    msg: &MsgConnectionOpenTry,
) -> Result<DeliveryOutcome, Error> {
    // Check that consensus height (for client proof) in message is not too advanced nor too old.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Proof verification in two steps:
    // 1. Setup: build the ConnectionEnd as we expect to find it on the other party.
    let mut expected_conn = ConnectionEnd::new(
        msg.counterparty().client_id().clone(),
        Counterparty::new(
            msg.client_id().as_str().into(),
            msg.connection_id().as_str().into(),
            ctx.commitment_prefix(),
        )?,
        msg.counterparty_versions(),
    )?;
    expected_conn.set_state(State::Init);
    // 2. Pass the details to our verification function.
    verify_proofs(ctx, expected_conn, msg.proofs())?;

    // Unwrap the old connection end (if any) and validate it against the message.
    let mut new_conn = match ctx.current_connection() {
        Some(old_conn_end) => {
            // Validate that existing connection end matches with the one we're trying to establish.
            if old_conn_end.state_matches(&State::Init)
                && old_conn_end.counterparty_matches(&msg.counterparty())
                && old_conn_end.client_id_matches(msg.client_id())
            {
                // A ConnectionEnd already exists and all validation passed.
                Ok(old_conn_end.clone())
            } else {
                // A ConnectionEnd already exists and validation failed.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            }
        }
        // No ConnectionEnd exists for this ConnectionId. Create & return a new one.
        None => Ok(ConnectionEnd::new(
            msg.client_id().clone(),
            msg.counterparty().clone(),
            msg.counterparty_versions(),
        )?),
    }?;

    // Transition the connection end to the new state & pick a version.
    new_conn.set_state(State::TryOpen);
    new_conn.set_version(pick_version(msg.counterparty_versions()).unwrap());
    // TODO: fix version unwrap above.

    Ok(new_conn)
}

fn deliver_ack_msg(
    ctx: &ICS3Context,
    msg: &MsgConnectionOpenAck,
) -> Result<DeliveryOutcome, Error> {
    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn = match ctx.current_connection() {
        // A connection end must exist and must be Init or TryOpen; otherwise we return an error.
        Some(old_conn_end) => {
            if !(old_conn_end.state_matches(&State::Init)
                || old_conn_end.state_matches(&State::TryOpen))
            {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(
                Kind::UninitializedConnection.context(msg.connection_id().to_string()),
            ))
        }
    }?;

    // Proof verification.
    let mut expected_conn = ConnectionEnd::new(
        new_conn.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is The local chain.
            new_conn.client_id(),                // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            ctx.commitment_prefix(),             // Local commitment prefix.
        )?,
        vec![msg.version().clone()],
    )?;
    expected_conn.set_state(State::TryOpen);
    // 2. Pass the details to our verification function.
    verify_proofs(ctx, expected_conn, msg.proofs())?;

    new_conn.set_state(State::Open);
    new_conn.set_version(msg.version().clone());

    Ok(new_conn)
}

fn deliver_confirm_msg(
    ctx: &ICS3Context,
    msg: &MsgConnectionOpenConfirm,
) -> Result<DeliveryOutcome, Error> {
    // Unwrap the old connection end & validate it.
    let mut new_conn = match ctx.current_connection() {
        // A connection end must exist and must be in TryOpen state; otherwise return error.
        Some(old_conn_end) => {
            if !(old_conn_end.state_matches(&State::TryOpen)) {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(
                    Kind::ConnectionMismatch.context(msg.connection_id().to_string()),
                ))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(
                Kind::UninitializedConnection.context(msg.connection_id().to_string()),
            ))
        }
    }?;

    // Verify proofs.
    let mut expected_conn = ConnectionEnd::new(
        new_conn.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is the local chain.
            new_conn.client_id(),                // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            ctx.commitment_prefix(),             // Local commitment prefix.
        )?,
        new_conn.versions(),
    )?;
    expected_conn.set_state(State::Open);
    // 2. Pass the details to our verification function.
    verify_proofs(ctx, expected_conn, msg.proofs())?;

    new_conn.set_state(State::Open);

    Ok(new_conn)
}

fn verify_proofs(
    _ctx: &ICS3Context,
    _expected_conn: ConnectionEnd,
    _proofs: &Proofs,
) -> Result<(), Error> {
    // TODO. Authenticity and semantic (validity) checks, roughly speaking:
    // - client consensus state (must match our own state for the given height)
    // - connection state (must match _expected_conn)

    Ok(())
}

fn check_client_consensus_height(ctx: &ICS3Context, claimed_height: Height) -> Result<(), Error> {
    if claimed_height > ctx.chain_current_height() {
        // Fail if the consensus height is too advanced.
        Err(Kind::InvalidConsensusHeight
            .context(claimed_height.to_string())
            .into())
    } else if claimed_height < (ctx.chain_current_height() - ctx.chain_trusting_period()) {
        // Fail if the consensus height is too old (outside of trusting period).
        Err(Kind::StaleConsensusHeight
            .context(claimed_height.to_string())
            .into())
    } else {
        Ok(())
    }
}

pub fn produce_events(ctx: &ICS3Context, msg: &ICS3Msg) -> Vec<IBCEvent> {
    let event = match msg {
        ICS3Msg::ConnectionOpenInit(msg) => OpenInitConnection(ConnectionEvents::OpenInit {
            height: ctx.chain_current_height().into(),
            connection_id: ctx.current_connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenTry(msg) => OpenTryConnection(ConnectionEvents::OpenTry {
            height: ctx.chain_current_height().into(),
            connection_id: ctx.current_connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenAck(_) => OpenAckConnection(ConnectionEvents::OpenAck {
            height: ctx.chain_current_height().into(),
            connection_id: ctx.current_connection_id().clone(),
        }),
        ICS3Msg::ConnectionOpenConfirm(_) => OpenConfirmConnection(ConnectionEvents::OpenConfirm {
            height: ctx.chain_current_height().into(),
            connection_id: ctx.current_connection_id().clone(),
        }),
    };

    vec![event]
}
