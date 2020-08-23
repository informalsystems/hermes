use crate::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use crate::ics03_connection::context::ICS3Context;
use crate::ics03_connection::error::{Error, Kind};
use crate::ics03_connection::handler::verify::verify_proofs;
use crate::ics03_connection::handler::Object;
use crate::ics03_connection::msgs::MsgConnectionOpenConfirm;

/// Protocol logic specific to delivering ICS3 messages of type `MsgConnectionOpenConfirm`.
pub(crate) fn process(
    ctx: &dyn ICS3Context,
    msg: &MsgConnectionOpenConfirm,
) -> Result<Object, Error> {
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
    // 2. Pass the details to the verification function.
    verify_proofs(
        ctx,
        msg.connection_id(),
        &new_conn,
        &expected_conn,
        msg.proofs(),
    )?;

    new_conn.set_state(State::Open);

    Ok(new_conn)
}
