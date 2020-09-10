use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::{check_client_consensus_height, verify_proofs};
use crate::ics03_connection::handler::ConnectionEvent::ConnOpenAck;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::msgs::MsgConnectionOpenAck;

/// Protocol logic specific to processing ICS3 messages of type `MsgConnectionOpenAck`.
pub(crate) fn process(
    ctx: &dyn ConnectionReader,
    msg: MsgConnectionOpenAck,
) -> HandlerResult<ConnectionResult, Error> {
    let mut output = HandlerOutput::builder();

    // Check the client's (consensus state) proof height.
    check_client_consensus_height(ctx, msg.consensus_height())?;

    // Unwrap the old connection end & validate it.
    let mut new_conn_end = match ctx.fetch_connection_end(msg.connection_id()) {
        // A connection end must exist and must be Init or TryOpen; otherwise we return an error.
        Some(old_conn_end) => {
            if !((old_conn_end.state_matches(&State::Init)
                && old_conn_end.versions().contains(msg.version()))
                || (old_conn_end.state_matches(&State::TryOpen)
                    && old_conn_end.versions().get(0).eq(&Some(msg.version()))))
            {
                // Old connection end is in incorrect state, propagate the error.
                Err(Into::<Error>::into(Kind::ConnectionMismatch(
                    msg.connection_id().clone(),
                )))
            } else {
                Ok(old_conn_end.clone())
            }
        }
        None => {
            // No connection end exists for this conn. identifier. Impossible to continue handshake.
            Err(Into::<Error>::into(Kind::UninitializedConnection(
                msg.connection_id().clone(),
            )))
        }
    }?;

    // Proof verification.
    let expected_conn = ConnectionEnd::new(
        State::TryOpen,
        new_conn_end.counterparty().client_id().clone(),
        Counterparty::new(
            // The counterparty is the local chain.
            new_conn_end.client_id().clone(), // The local client identifier.
            msg.connection_id().clone(),      // Local connection id.
            ctx.commitment_prefix(),          // Local commitment prefix.
        )?,
        vec![msg.version().clone()], // TODO: ICS03 VERSION NEGOTIATION BUG FIX.
    )?;
    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.connection_id(),
        &new_conn_end,
        &expected_conn,
        msg.proofs(),
    )?;

    output.log("success: connection verification passed");

    new_conn_end.set_state(State::Open);
    new_conn_end.set_version(msg.version().clone());

    let result = ConnectionResult {
        connection_end: new_conn_end,
        connection_id: msg.connection_id().clone(),
    };

    output.emit(ConnOpenAck(result.clone()));

    Ok(output.with_result(result))
}

pub fn keep(keeper: &mut dyn ConnectionKeeper, result: ConnectionResult) -> Result<(), Error> {
    keeper.store_connection(&result.connection_id, &result.connection_end)?;
    Ok(())
}
