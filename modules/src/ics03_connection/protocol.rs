//! This module implements the protocol for ICS3, that is, the processing logic for ICS3
//! connection open handshake messages.
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
// use crate::ics07_tendermint::consensus_state::ConsensusState;
use crate::proofs::Proofs;
use crate::Height;

type ProtocolResult = Result<ProtocolOutput, Error>;

#[derive(Debug, Clone, Default)]
pub struct ProtocolOutput {
    object: Option<Output>, // Vec<u8>? Data?
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

// The outcome after processing (delivering) a specific ICS3 message.
type Output = ConnectionEnd;

/// General entry point for delivering (i.e., processing) any type of message related to the ICS3
/// connection open handshake protocol.
pub fn process_ics3_msg(ctx: &dyn ICS3Context, message: &ICS3Msg) -> ProtocolResult {
    // Process each message with the corresponding process_*_msg function.
    // After processing a specific message, the output consists of a ConnectionEnd.
    let conn_object = match message {
        ICS3Msg::ConnectionOpenInit(msg) => process_init_msg(ctx, msg),
        ICS3Msg::ConnectionOpenTry(msg) => process_try_msg(ctx, msg),
        ICS3Msg::ConnectionOpenAck(msg) => process_ack_msg(ctx, msg),
        ICS3Msg::ConnectionOpenConfirm(msg) => process_confirm_msg(ctx, msg),
    }?;

    // Post-processing: emit events.
    let mut events = produce_events(ctx, message);

    Ok(ProtocolOutput::new()
        .set_object(conn_object)
        .add_events(&mut events))
}

/// Protocol logic specific to ICS3 messages of type `MsgConnectionOpenInit`.
fn process_init_msg(ctx: &dyn ICS3Context, msg: &MsgConnectionOpenInit) -> Result<Output, Error> {
    // No connection should exist.
    if ctx.fetch_connection_end(msg.connection_id()).is_some() {
        Err(Kind::ConnectionExistsAlready(msg.connection_id().clone()).into())
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

/// Protocol logic specific to delivering ICS3 messages of type `MsgConnectionOpenTry`.
fn process_try_msg(ctx: &dyn ICS3Context, msg: &MsgConnectionOpenTry) -> Result<Output, Error> {
    // Check that consensus height (for client proof) in message is not too advanced nor too old.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end (if any) and validate it against the message.
    let mut new_conn = match ctx.fetch_connection_end(msg.connection_id()) {
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
    verify_proofs(ctx, &new_conn, &expected_conn, msg.proofs())?;

    // Transition the connection end to the new state & pick a version.
    new_conn.set_state(State::TryOpen);
    new_conn.set_version(pick_version(msg.counterparty_versions()).unwrap());
    // TODO: fix version unwrap above.

    Ok(new_conn)
}

/// Protocol logic specific to delivering ICS3 messages of type `MsgConnectionOpenAck`.
fn process_ack_msg(ctx: &dyn ICS3Context, msg: &MsgConnectionOpenAck) -> Result<Output, Error> {
    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn = match ctx.fetch_connection_end(msg.connection_id()) {
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
            new_conn.client_id().to_string(), // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            ctx.commitment_prefix(),          // Local commitment prefix.
        )?,
        vec![msg.version().clone()],
    )?;
    expected_conn.set_state(State::TryOpen);
    // 2. Pass the details to our verification function.
    verify_proofs(ctx, &new_conn, &expected_conn, msg.proofs())?;

    new_conn.set_state(State::Open);
    new_conn.set_version(msg.version().clone());

    Ok(new_conn)
}

/// Protocol logic specific to delivering ICS3 messages of type `MsgConnectionOpenConfirm`.
fn process_confirm_msg(
    ctx: &dyn ICS3Context,
    msg: &MsgConnectionOpenConfirm,
) -> Result<Output, Error> {
    // Unwrap the old connection end & validate it.
    let mut new_conn = match ctx.fetch_connection_end(msg.connection_id()) {
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
            new_conn.client_id().to_string(), // The local client identifier.
            msg.connection_id().as_str().into(), // Local connection id.
            ctx.commitment_prefix(),          // Local commitment prefix.
        )?,
        new_conn.versions(),
    )?;
    expected_conn.set_state(State::Open);
    // 2. Pass the details to our verification function.
    verify_proofs(ctx, &new_conn, &expected_conn, msg.proofs())?;

    new_conn.set_state(State::Open);

    Ok(new_conn)
}

fn verify_proofs(
    ctx: &dyn ICS3Context,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    // Fetch the client state (IBC client on the local chain).
    let client = ctx
        .fetch_client_state(connection_end.client_id())
        .ok_or_else(|| Kind::MissingClient.context(connection_end.client_id().to_string()))?;

    // Verify the proof for the connection state against the expected connection end.
    let verification_res = client.verify_connection_state(
        proofs.height(),
        connection_end.counterparty().prefix(),
        proofs.object_proof(),
        connection_end.counterparty().connection_id(),
        expected_conn,
    )?;
    if verification_res == false {
        // Verification of connection state proof failed.
        return Err(Kind::InvalidProof
            .context(String::from("connection state proof is invalid"))
            .into());
    }

    // Verify the proof for the client's consensus state.
    // The `consensus_proof` may be missing. If so, return Ok(()); otherwise, verify the proof.
    proofs.consensus_proof().map_or(Ok(()), |consensus_proof| {
        // Search for the expected consensus state.
        match ctx.fetch_consensus_state(consensus_proof.height()) {
            Some(expected_cs) => {
                let verification_res = client.verify_client_consensus_state(
                    proofs.height(),
                    connection_end.counterparty().prefix(),
                    &consensus_proof.proof(),
                    connection_end.counterparty().client_id(),
                    consensus_proof.height(),
                    expected_cs,
                )?;
                if verification_res == false {
                    Err(Kind::InvalidProof
                        .context(String::from("consensus state proof is invalid"))
                        .into())
                } else {
                    Ok(())
                }
            }
            // The consensus state at the given height was not found.
            // It would be bizarre if this happens, but catch it gracefully anyhow.
            None => Err(Kind::ErrorFetchingConsensusState
                .context(consensus_proof.height().to_string())
                .into()),
        }
    })
}

fn check_client_consensus_height(
    ctx: &dyn ICS3Context,
    claimed_height: Height,
) -> Result<(), Error> {
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

/// Given a context and a message, produces the corresponding events.
pub fn produce_events(ctx: &dyn ICS3Context, msg: &ICS3Msg) -> Vec<IBCEvent> {
    let event = match msg {
        ICS3Msg::ConnectionOpenInit(msg) => OpenInitConnection(ConnectionEvents::OpenInit {
            height: ctx.chain_current_height().into(),
            connection_id: msg.connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenTry(msg) => OpenTryConnection(ConnectionEvents::OpenTry {
            height: ctx.chain_current_height().into(),
            connection_id: msg.connection_id().clone(),
            client_id: msg.client_id().clone(),
            counterparty_client_id: msg.counterparty().client_id().clone(),
        }),
        ICS3Msg::ConnectionOpenAck(msg) => OpenAckConnection(ConnectionEvents::OpenAck {
            height: ctx.chain_current_height().into(),
            connection_id: msg.connection_id().clone(),
        }),
        ICS3Msg::ConnectionOpenConfirm(msg) => {
            OpenConfirmConnection(ConnectionEvents::OpenConfirm {
                height: ctx.chain_current_height().into(),
                connection_id: msg.connection_id().clone(),
            })
        }
    };

    vec![event]
}

#[cfg(test)]
mod tests {
    use crate::ics02_client::state::{ClientState, ConsensusState};
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::ctx::{Context, ICS3Context};
    use crate::ics03_connection::error::Error;
    use crate::ics03_connection::msgs::ICS3Msg;
    use crate::ics03_connection::protocol::process_init_msg;
    use crate::ics23_commitment::CommitmentPrefix;
    use crate::ics24_host::identifier::{ClientId, ConnectionId};

    #[derive(Clone, Debug, Default)]
    struct MockContext {}
    impl ICS3Context for MockContext {
        fn fetch_connection_end(&self, _cid: &ConnectionId) -> Option<&ConnectionEnd> {
            unimplemented!()
        }

        fn fetch_client_state(
            &self,
            client_id: &ClientId,
        ) -> Option<&dyn ClientState<ValidationError = Error>> {
            unimplemented!()
        }

        fn chain_current_height(&self) -> u64 {
            unimplemented!()
        }

        fn chain_trusting_period(&self) -> u64 {
            unimplemented!()
        }

        fn commitment_prefix(&self) -> CommitmentPrefix {
            unimplemented!()
        }

        fn fetch_consensus_state(
            &self,
            height: u64,
        ) -> Option<&dyn ConsensusState<ValidationError = Error>> {
            unimplemented!()
        }
    }
    impl MockContext {
        fn new() -> Self {
            Self::default()
        }
    }

    fn get_dummy_ics_msg() -> ICS3Msg {
        unimplemented!()
    }

    #[test]
    fn conn_open_init_msg_processing() {
        #[derive(Clone, Debug, PartialEq)]
        struct ConOpenInitProcessParams {
            ctx: MockContext,
            msg: ICS3Msg,
        }

        struct Test {
            name: String,
            params: ConOpenInitProcessParams,
            want_pass: bool,
        }

        let default_con_params = ConOpenInitProcessParams {
            ctx: MockContext::new(),
            msg: get_dummy_ics_msg(),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad parameters".to_string(),
                params: ConOpenInitProcessParams {
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            // let res = process_init_msg(p.ctx, p.msg);

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "process_init_msg() failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
