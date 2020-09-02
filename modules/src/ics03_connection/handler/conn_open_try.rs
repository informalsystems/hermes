use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{pick_version, ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::ConnectionReader;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::{check_client_consensus_height, verify_proofs};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenTry;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::MsgConnectionOpenTry;

/// Protocol logic specific to delivering ICS3 messages of type `MsgConnectionOpenTry`.
pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenTry,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check that consensus height (for client proof) in message is not too advanced nor too old.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end (if any) and validate it against the message.
    let mut new_connection_end = match ctx.fetch_connection_end(msg.connection_id()) {
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
            State::Init,
            msg.client_id().clone(),
            msg.counterparty(),
            msg.counterparty_versions(),
        )?),
    }?;

    // Proof verification in two steps:
    // 1. Setup: build the ConnectionEnd as we expect to find it on the other party.
    let expected_conn = ConnectionEnd::new(
        State::Init,
        msg.counterparty().client_id().clone(),
        Counterparty::new(
            msg.client_id().clone(),
            msg.connection_id().clone(),
            ctx.commitment_prefix(),
        )?,
        msg.counterparty_versions(),
    )?;

    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.connection_id(),
        &new_connection_end,
        &expected_conn,
        msg.proofs(),
    )?;

    // Transition the connection end to the new state & pick a version.
    new_connection_end.set_state(State::TryOpen);
    new_connection_end.set_version(pick_version(msg.counterparty_versions()).unwrap());
    // TODO: fix version unwrap above.

    output.log("success: connection verification passed");

    let result = ConnectionResult {
        connection_id: msg.connection_id().clone(),
        connection_end: new_connection_end,
    };

    output.emit(ConnOpenTry(result.clone()));

    Ok(output.with_result(result))
}
