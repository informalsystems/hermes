//! Protocol logic specific to ICS4 messages of type `MsgChannelOpenConfirm`.
use crate::core::ics03_connection::connection::State as ConnectionState;
use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, State};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::error::Error;
use crate::core::ics04_channel::events::Attributes;
use crate::core::ics04_channel::handler::verify::verify_channel_proofs;
use crate::core::ics04_channel::handler::{ChannelIdState, ChannelResult};
use crate::core::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;

pub(crate) fn process<Ctx: ChannelReader>(
    ctx: &Ctx,
    msg: &MsgChannelOpenConfirm,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    // Unwrap the old channel end and validate it against the message.
    let mut channel_end = ctx.channel_end(&msg.port_id, &msg.channel_id)?;

    // Validate that the channel end is in a state where it can be confirmed.
    if !channel_end.state_matches(&State::TryOpen) {
        return Err(Error::invalid_channel_state(
            msg.channel_id.clone(),
            channel_end.state,
        ));
    }

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

    let expected_counterparty =
        Counterparty::new(msg.port_id.clone(), Some(msg.channel_id.clone()));

    let connection_counterparty = conn.counterparty();
    let ccid = connection_counterparty.connection_id().ok_or_else(|| {
        Error::undefined_connection_counterparty(channel_end.connection_hops()[0].clone())
    })?;

    let expected_connection_hops = vec![ccid.clone()];

    let expected_channel_end = ChannelEnd::new(
        State::Open,
        *channel_end.ordering(),
        expected_counterparty,
        expected_connection_hops,
        channel_end.version().clone(),
    );
    //2. Verify proofs
    verify_channel_proofs(
        ctx,
        msg.proofs.height(),
        &channel_end,
        &conn,
        &expected_channel_end,
        &msg.proofs,
    )
    .map_err(Error::chan_open_confirm_proof_verification)?;

    output.log("success: channel open confirm ");

    // Transition the channel end to the new state.
    channel_end.set_state(State::Open);

    let result = ChannelResult {
        port_id: msg.port_id.clone(),
        channel_id: msg.channel_id.clone(),
        channel_id_state: ChannelIdState::Reused,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: Some(msg.channel_id.clone()),
        ..Default::default()
    };
    output.emit(IbcEvent::OpenConfirmChannel(
        event_attributes
            .try_into()
            .map_err(|_| Error::missing_channel_id())?,
    ));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    use test_log::test;

    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics03_connection::connection::ConnectionEnd;
    use crate::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
    use crate::core::ics03_connection::connection::State as ConnectionState;
    use crate::core::ics03_connection::context::ConnectionReader;
    use crate::core::ics03_connection::msgs::test_util::get_dummy_raw_counterparty;
    use crate::core::ics03_connection::version::get_compatible_versions;
    use crate::core::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
    use crate::core::ics04_channel::handler::channel_dispatch;
    use crate::core::ics04_channel::msgs::chan_open_confirm::test_util::get_dummy_raw_msg_chan_open_confirm;
    use crate::core::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
    use crate::core::ics04_channel::msgs::ChannelMsg;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::{ClientId, ConnectionId};
    use crate::events::IbcEvent;
    use crate::mock::context::MockContext;
    use crate::timestamp::ZERO_DURATION;
    use crate::Height;

    // TODO: The tests here should use the same structure as `handler::chan_open_try::tests`.
    #[test]
    fn chan_open_confirm_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }
        let client_id = ClientId::new(ClientType::Mock, 24).unwrap();
        let conn_id = ConnectionId::new(2);
        let context = MockContext::default();
        let client_consensus_state_height = context.host_current_height().revision_height();

        // The connection underlying the channel we're trying to open.
        let conn_end = ConnectionEnd::new(
            ConnectionState::Open,
            client_id.clone(),
            ConnectionCounterparty::try_from(get_dummy_raw_counterparty()).unwrap(),
            get_compatible_versions(),
            ZERO_DURATION,
        );

        let msg_chan_confirm = MsgChannelOpenConfirm::try_from(
            get_dummy_raw_msg_chan_open_confirm(client_consensus_state_height),
        )
        .unwrap();

        let chan_end = ChannelEnd::new(
            State::TryOpen,
            Order::default(),
            Counterparty::new(
                msg_chan_confirm.port_id.clone(),
                Some(msg_chan_confirm.channel_id.clone()),
            ),
            vec![conn_id.clone()],
            Version::default(),
        );

        let tests: Vec<Test> = vec![Test {
            name: "Good parameters".to_string(),
            ctx: context
                .with_client(
                    &client_id,
                    Height::new(0, client_consensus_state_height).unwrap(),
                )
                .with_connection(conn_id, conn_end)
                .with_channel(
                    msg_chan_confirm.port_id.clone(),
                    msg_chan_confirm.channel_id.clone(),
                    chan_end,
                ),
            msg: ChannelMsg::ChannelOpenConfirm(msg_chan_confirm),
            want_pass: true,
        }]
        .into_iter()
        .collect();

        for test in tests {
            let res = channel_dispatch(&test.ctx, &test.msg);
            // Additionally check the events and the output objects in the result.
            match res {
                Ok((proto_output, res)) => {
                    assert!(
                            test.want_pass,
                            "chan_open_confirm: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                            test.name,
                            test.msg,
                            test.ctx.clone()
                        );

                    let proto_output = proto_output.with_result(());
                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // The object in the output is a ConnectionEnd, should have init state.
                    //assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                    assert_eq!(res.channel_end.state().clone(), State::Open);

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::OpenConfirmChannel(_)));
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "chan_open_ack: did not pass test: {}, \nparams {:?} {:?}\nerror: {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
