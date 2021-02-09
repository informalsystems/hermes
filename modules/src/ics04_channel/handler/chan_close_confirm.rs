//! Protocol logic specific to ICS4 messages of type `MsgChannelCloseInit`.
use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::State as ConnectionState;
use crate::ics04_channel::channel::State;
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::events::Attributes;
use crate::ics04_channel::handler::verify::verify_proofs;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use crate::{
    events::IBCEvent,
    ics04_channel::channel::{ChannelEnd, Counterparty},
};
use Kind::ConnectionNotOpen;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelCloseConfirm,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    // Retrieve the old channel end and validate it against the message.

    let mut channel_end = ctx
        .channel_end(&(msg.port_id().clone(), msg.channel_id().clone()))
        .ok_or_else(|| Kind::ChannelNotFound.context(msg.channel_id().clone().to_string()))?;

    // Validate that the channel end is in a state where it can be closed.
    if channel_end.state_matches(&State::Closed) {
        return Err(Kind::ChannelAlreadyClosed(msg.channel_id().clone()).into());
    }

    // Channel capabilities
    let channel_cap = ctx.authenticated_capability(&msg.port_id().clone())?;

    // An OPEN IBC connection running on the local (host) chain should exist.
    if channel_end.connection_hops().len() != 1 {
        return Err(Kind::InvalidConnectionHopsLength.into());
    }
    let conn = ctx
        .connection_end(&channel_end.connection_hops()[0])
        .ok_or_else(|| Kind::MissingConnection(channel_end.connection_hops()[0].clone()))?;
    if !conn.state_matches(&ConnectionState::Open) {
        return Err(ConnectionNotOpen(channel_end.connection_hops()[0].clone()).into());
    }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_counterparty =
        Counterparty::new(msg.port_id().clone(), Some(msg.channel_id().clone()));

    let counterparty = conn.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        Kind::UndefinedConnectionCounterparty(channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Closed,
        *channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        channel_end.version(),
    );

    verify_proofs(
        ctx,
        &channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs(),
    )
    .map_err(|e| Kind::FailedChanneOpenTryVerification.context(e))?;

    output.log("success: channel close confirm ");

    // Transition the channel end to the new state & pick a version.
    channel_end.set_state(State::Closed);

    let result = ChannelResult {
        port_id: msg.port_id().clone(),
        channel_id: Some(msg.channel_id().clone()),
        channel_cap,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(msg.channel_id().clone()),
        ..Default::default()
    };
    output.emit(IBCEvent::CloseConfirmChannel(event_attributes.into()));

    Ok(output.with_result(result))
}
