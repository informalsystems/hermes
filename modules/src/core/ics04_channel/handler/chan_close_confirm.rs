//! Protocol logic specific to ICS4 messages of type `MsgChannelCloseConfirm`.
use crate::core::ics03_connection::connection::State as ConnectionState;
use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, State};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::events::Attributes;
use crate::core::ics04_channel::handler::verify::verify_channel_proofs;
use crate::core::ics04_channel::handler::{ChannelIdState, ChannelResult};
use crate::core::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: &MsgChannelCloseConfirm,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    // Retrieve the old channel end and validate it against the message.
    let mut channel_end = ctx.channel_end(&(msg.port_id.clone(), msg.channel_id))?;

    // Validate that the channel end is in a state where it can be closed.
    if channel_end.state_matches(&State::Closed) {
        return Err(Error::channel_closed(msg.channel_id));
    }

    // Channel capabilities
    let channel_cap = ctx.authenticated_capability(&msg.port_id)?;

    // An OPEN IBC connection running on the local (host) chain should exist.
    if channel_end.connection_hops().len() != 1 {
        return Err(Error::invalid_connection_hops_length(
            1,
            channel_end.connection_hops().len(),
        ));
    }

    let conn = ctx.connection_end(&channel_end.connection_hops()[0])?;

    if !conn.state_matches(&ConnectionState::Open) {
        return Err(Error::connection_not_open(
            channel_end.connection_hops()[0].clone(),
        ));
    }

    // Proof verification in two steps:
    // 1. Setup: build the Channel as we expect to find it on the other party.

    let expected_counterparty = Counterparty::new(msg.port_id.clone(), Some(msg.channel_id));

    let counterparty = conn.counterparty();
    let ccid = counterparty.connection_id().ok_or_else(|| {
        Error::undefined_connection_counterparty(channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Closed,
        *channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        channel_end.version().clone(),
    );

    verify_channel_proofs(
        ctx,
        msg.proofs.height(),
        &channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs,
    )?;

    output.log("success: channel close confirm ");

    // Transition the channel end to the new state & pick a version.
    channel_end.set_state(State::Closed);

    let result = ChannelResult {
        port_id: msg.port_id.clone(),
        channel_id: msg.channel_id,
        channel_id_state: ChannelIdState::Reused,
        channel_cap,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(msg.channel_id),
        height: ctx.host_height(),
        ..Default::default()
    };
    output.emit(IbcEvent::CloseConfirmChannel(
        event_attributes
            .try_into()
            .map_err(|_| Error::missing_channel_id())?,
    ));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::core::ics04_channel::context::ChannelReader;
    use crate::core::ics04_channel::msgs::chan_close_confirm::test_util::get_dummy_raw_msg_chan_close_confirm;
    use crate::core::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
    use crate::core::ics04_channel::msgs::ChannelMsg;
    use crate::events::IbcEvent;
    use crate::prelude::*;

    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics03_connection::connection::ConnectionEnd;
    use crate::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::core::ics03_connection::connection::State as ConnectionState;
    use crate::core::ics03_connection::msgs::test_util::get_dummy_raw_counterparty;
    use crate::core::ics03_connection::version::get_compatible_versions;
    use crate::core::ics04_channel::channel::{
        ChannelEnd, Counterparty, Order, State as ChannelState,
    };
    use crate::core::ics04_channel::handler::channel_dispatch;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::{ClientId, ConnectionId};

    use crate::mock::context::MockContext;
    use crate::timestamp::ZERO_DURATION;

    #[test]
    fn chan_close_confirm_event_height() {
        let client_id = ClientId::new(ClientType::Mock, 24).unwrap();
        let conn_id = ConnectionId::new(2);
        let default_context = MockContext::default();
        let client_consensus_state_height = default_context.host_height();

        let conn_end = ConnectionEnd::new(
            ConnectionState::Open,
            client_id.clone(),
            ConnectionCounterparty::try_from(get_dummy_raw_counterparty()).unwrap(),
            get_compatible_versions(),
            ZERO_DURATION,
        );

        let msg_chan_close_confirm = MsgChannelCloseConfirm::try_from(
            get_dummy_raw_msg_chan_close_confirm(client_consensus_state_height.revision_height),
        )
        .unwrap();

        let chan_end = ChannelEnd::new(
            ChannelState::Open,
            Order::default(),
            Counterparty::new(
                msg_chan_close_confirm.port_id.clone(),
                Some(msg_chan_close_confirm.channel_id),
            ),
            vec![conn_id.clone()],
            Version::default(),
        );

        let context = default_context
            .with_client(&client_id, client_consensus_state_height)
            .with_connection(conn_id, conn_end)
            .with_port_capability(msg_chan_close_confirm.port_id.clone())
            .with_channel(
                msg_chan_close_confirm.port_id.clone(),
                msg_chan_close_confirm.channel_id,
                chan_end,
            );

        let (handler_output_builder, _) = channel_dispatch(
            &context,
            &ChannelMsg::ChannelCloseConfirm(msg_chan_close_confirm),
        )
        .unwrap();

        let handler_output = handler_output_builder.with_result(());

        assert!(!handler_output.events.is_empty()); // Some events must exist.

        for event in handler_output.events.iter() {
            assert!(matches!(event, &IbcEvent::CloseConfirmChannel(_)));
            assert_eq!(event.height(), context.host_height());
        }
    }
}
