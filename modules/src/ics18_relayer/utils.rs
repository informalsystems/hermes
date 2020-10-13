use crate::ics02_client::client_def::AnyHeader;
use crate::ics02_client::header::Header;
use crate::ics02_client::msgs::{ClientMsg, MsgUpdateAnyClient};
use crate::ics02_client::state::ClientState;
use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics18_relayer::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;

/// Creates a `ClientMsg::UpdateClient` for a client with id `client_id` running on the `dest`
/// context, assuming that the latest header on the source context is `src_header`.
pub fn create_client_update_datagram<Ctx>(
    dest: &Ctx,
    client_id: &ClientId,
    src_header: AnyHeader,
) -> Result<ClientMsg, Error>
where
    Ctx: ICS18Context,
{
    // Check if client for ibc0 on ibc1 has been updated to latest height:
    // - query client state on destination chain
    let dest_client_state = dest
        .query_client_full_state(&client_id)
        .ok_or_else(|| Kind::ClientStateNotFound(client_id.clone()))?;

    let dest_client_latest_height = dest_client_state.latest_height();

    if src_header.height() == dest_client_latest_height {
        return Err(Kind::ClientAlreadyUpToDate(
            client_id.clone(),
            src_header.height(),
            dest_client_latest_height,
        )
        .into());
    };

    if dest_client_latest_height > src_header.height() {
        return Err(Kind::ClientAtHeigherHeight(
            client_id.clone(),
            src_header.height(),
            dest_client_latest_height,
        )
        .into());
    };

    // Client on destination chain can be updated.
    Ok(ClientMsg::UpdateClient(MsgUpdateAnyClient {
        client_id: client_id.clone(),
        header: src_header,
        signer: get_dummy_account_id(),
    }))
}

#[cfg(test)]
mod tests {
    use crate::ics02_client::state::ClientState;
    use crate::ics18_relayer::context::ICS18Context;
    use crate::ics18_relayer::context_mock::MockICS18Context;
    use crate::ics18_relayer::utils::create_client_update_datagram;
    use crate::ics24_host::identifier::ClientId;
    use crate::ics26_routing::msgs::ICS26Envelope;

    use std::str::FromStr;

    #[test]
    /// Serves to test both ICS 26 `dispatch` & `create_client_update_datagram` function.
    /// Implements a "ping pong" of client update messages, so that two chains repeatedly
    /// process a client update message and update their height in succession.
    fn client_update_ping_pong() {
        let chain_id = "testchain-0".to_string();

        let chain_a_start_height = 11;
        let chain_b_start_height = 20;
        let client_on_b_for_a_height = 10; // Should be smaller than `chain_a_start_height`
        let client_on_a_for_b_height = 20; // Should be smaller than `chain_b_start_height`
        let max_history_size = 3;
        let num_iterations = 4;

        let client_on_a_for_b = ClientId::from_str("ibconeclient").unwrap();
        let client_on_b_for_a = ClientId::from_str("ibczeroclient").unwrap();

        // Create two mock contexts, one for each chain.
        let mut ctx_a = MockICS18Context::new(
            chain_id.clone(),
            chain_a_start_height,
            max_history_size,
            &client_on_a_for_b,
            client_on_a_for_b_height,
        );
        let mut ctx_b = MockICS18Context::new(
            chain_id,
            chain_b_start_height,
            max_history_size,
            &client_on_b_for_a,
            client_on_b_for_a_height,
        );

        for _i in 0..num_iterations {
            // Update client on chain B to latest height of A.
            // - create the client update message with the latest header from A
            let a_latest_header = ctx_a.query_latest_header().unwrap();
            let client_msg_b_res =
                create_client_update_datagram(&ctx_b, &client_on_b_for_a, a_latest_header);
            assert_eq!(
                client_msg_b_res.is_ok(),
                true,
                "create_client_update failed for context destination {:?}, error: {:?}",
                ctx_b,
                client_msg_b_res
            );
            let client_msg_b = client_msg_b_res.unwrap();

            // - send the message to B
            let dispatch_res_b = ctx_b.send(ICS26Envelope::ICS2Msg(client_msg_b));

            // Check if the update succeeded.
            assert!(dispatch_res_b.is_ok());
            let client_height_b = ctx_b
                .query_client_full_state(&client_on_b_for_a)
                .unwrap()
                .latest_height();
            assert_eq!(client_height_b, ctx_a.query_latest_height());

            // Update client on chain B to latest height of B.
            // - create the client update message with the latest header from B
            let b_latest_header = ctx_b.query_latest_header().unwrap();
            let client_msg_a_res =
                create_client_update_datagram(&ctx_a, &client_on_a_for_b, b_latest_header);
            assert_eq!(
                client_msg_a_res.is_ok(),
                true,
                "create_client_update failed for context destination {:?}, error: {:?}",
                ctx_a,
                client_msg_a_res
            );
            let client_msg_a = client_msg_a_res.unwrap();

            // - send the message to A
            let dispatch_res_a = ctx_a.send(ICS26Envelope::ICS2Msg(client_msg_a));

            // Check if the update succeeded.
            assert!(dispatch_res_a.is_ok());
            let client_height_a = ctx_a
                .query_client_full_state(&client_on_a_for_b)
                .unwrap()
                .latest_height();
            assert_eq!(client_height_a, ctx_b.query_latest_height());
        }
    }
}
