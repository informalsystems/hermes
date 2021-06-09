//! Protocol logic specific to ICS4 messages of type `MsgChannelCloseConfirm`.
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::State as ConnectionState;
use crate::ics04_channel::channel::{ChannelEnd, Counterparty, State};
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{self, ChannelError};
use crate::ics04_channel::events::Attributes;
use crate::ics04_channel::handler::verify::verify_channel_proofs;
use crate::ics04_channel::handler::{ChannelIdState, ChannelResult};
use crate::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use std::prelude::v1::*;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelCloseConfirm,
) -> HandlerResult<ChannelResult, ChannelError> {
    let mut output = HandlerOutput::builder();

    // Retrieve the old channel end and validate it against the message.
    let mut channel_end = ctx
        .channel_end(&(msg.port_id().clone(), msg.channel_id().clone()))
        .ok_or_else(|| {
            error::channel_not_found_error(
                msg.port_id.clone(),
                msg.channel_id().clone(),
                anyhow::anyhow!("channel end: channel not found error"),
            )
        })?;

    // Validate that the channel end is in a state where it can be closed.
    if channel_end.state_matches(&State::Closed) {
        return Err(error::channel_closed_error(msg.channel_id().clone()));
    }

    // Channel capabilities
    let channel_cap = ctx.authenticated_capability(&msg.port_id().clone())?;

    // An OPEN IBC connection running on the local (host) chain should exist.
    if channel_end.connection_hops().len() != 1 {
        return Err(error::invalid_connection_hops_length_error(
            1,
            channel_end.connection_hops().len(),
        ));
    }
    let conn = ctx
        .connection_end(&channel_end.connection_hops()[0])
        .ok_or_else(|| {
            error::missing_connection_error(anyhow::anyhow!(
                channel_end.connection_hops()[0].clone()
            ))
        })?;
    if !conn.state_matches(&ConnectionState::Open) {
        return Err(error::connection_not_open_error(
            channel_end.connection_hops()[0].clone(),
        ));
    }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_counterparty =
        Counterparty::new(msg.port_id().clone(), Some(msg.channel_id().clone()));

    let counterparty = conn.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        error::undefined_connection_counterparty_error(channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Closed,
        *channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        channel_end.version(),
    );

    verify_channel_proofs(
        ctx,
        &channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs(),
    )
    .map_err(|_| {
        error::failed_channe_open_try_verification_error(anyhow::anyhow!(
            "verify channel proof: failed channel open try verification error"
        ))
    })?;

    output.log("success: channel close confirm ");

    // Transition the channel end to the new state & pick a version.
    channel_end.set_state(State::Closed);

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_id: msg.channel_id().clone(),
        channel_id_state: ChannelIdState::Reused,
        channel_cap,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(msg.channel_id().clone()),
        ..Default::default()
    };
    output.emit(IbcEvent::CloseConfirmChannel(event_attributes.into()));

    Ok(output.with_result(result))
}
