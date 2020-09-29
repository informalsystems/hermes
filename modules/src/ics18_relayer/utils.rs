use crate::ics02_client::msgs::{ClientMsg, MsgUpdateAnyClient};
use crate::ics02_client::state::ClientState;
use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics18_relayer::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;
use crate::mock_client::header::MockHeader;

pub fn create_client_update_datagram<Ctx>(
    dest: &Ctx,
    src: &Ctx,
    client_id: &ClientId,
) -> Result<ClientMsg, Error>
where
    Ctx: ICS18Context,
{
    // Check if client for ibc0 on ibc1 has been updated to latest height:
    // - query latest height on source chain
    let src_latest_height = src.query_latest_height();
    // - query client state on destination chain
    let dest_client_state = dest
        .query_client_full_state(&client_id)
        .ok_or_else(|| Kind::ClientStateNotFound(client_id.clone()))?;

    let dest_client_latest_height = dest_client_state.latest_height();

    if dest_client_latest_height < src_latest_height {
        // Client on destination chain needs an update.
        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: MockHeader(src_latest_height).into(),
            signer: get_dummy_account_id(),
        };
        Ok(ClientMsg::UpdateClient(msg))
    } else {
        Err(Kind::ClientAlreadyUpToDate(
            client_id.clone(),
            src_latest_height,
            dest_client_latest_height,
        )
        .into())
    }
}

#[cfg(test)]
mod tests {
    use crate::ics02_client::state::ClientState;
    use crate::ics18_relayer::context::ICS18Context;
    use crate::ics18_relayer::context_mock::MockICS18Context;
    use crate::ics18_relayer::utils::create_client_update_datagram;
    use crate::ics24_host::identifier::ClientId;
    use crate::ics26_routing::handler::dispatch;
    use crate::ics26_routing::msgs::ICS26Envelope;
    use std::str::FromStr;
    use tendermint::block::Height;

    #[test]
    /// This test was moved here from ICS 26.
    /// Serves to test both ICS 26 `dispatch` & `create_client_update` function.
    fn client_update_ping_pong() {
        let chain_a_start_height = Height(11);
        let chain_b_start_height = Height(20);
        let client_on_b_for_a_height = Height(10); // Should be smaller than `chain_a_start_height`
        let client_on_a_for_b_height = Height(19); // Should be smaller than `chain_b_start_height`
        let max_history_size = 3;
        let num_iterations = 4;

        let client_on_a_for_b = ClientId::from_str("ibconeclient").unwrap();
        let client_on_b_for_a = ClientId::from_str("ibczeroclient").unwrap();

        // Create two mock contexts, one for each chain.
        let mut ctx_a = MockICS18Context::new(
            chain_a_start_height,
            max_history_size,
            &client_on_a_for_b,
            client_on_a_for_b_height,
        );
        let mut ctx_b = MockICS18Context::new(
            chain_b_start_height,
            max_history_size,
            &client_on_b_for_a,
            client_on_b_for_a_height,
        );

        for _i in 0..num_iterations {
            // Update client on chain B.
            let client_msg_b_res =
                create_client_update_datagram(&ctx_b, &ctx_a, &client_on_b_for_a);
            assert_eq!(
                client_msg_b_res.is_ok(),
                true,
                "create_client_update failed for context destination {:?}, error: {:?}",
                ctx_b,
                client_msg_b_res
            );
            let mut routing_context_b = ctx_b.routing_context().clone();
            let client_msg_b = client_msg_b_res.unwrap();
            let dispatch_res_b =
                dispatch(&mut routing_context_b, ICS26Envelope::ICS2Msg(client_msg_b));
            assert!(dispatch_res_b.is_ok());
            ctx_b.set_routing_context(routing_context_b); // Replace the original routing context with the updated one.

            // Check if the update succeeded.
            let client_height_b = ctx_b
                .query_client_full_state(&client_on_b_for_a)
                .unwrap()
                .latest_height();

            assert_eq!(client_height_b, ctx_a.query_latest_height());

            // Advance height on chain B.
            ctx_b.advance_chain_height();

            // Update client on chain A.
            let client_msg_a_res =
                create_client_update_datagram(&ctx_a, &ctx_b, &client_on_a_for_b);
            assert_eq!(
                client_msg_a_res.is_ok(),
                true,
                "create_client_update failed for context destination {:?}, error: {:?}",
                ctx_a,
                client_msg_a_res
            );
            let mut routing_context_a = ctx_a.routing_context().clone();
            let client_msg_a = client_msg_a_res.unwrap();
            let dispatch_res_a =
                dispatch(&mut routing_context_a, ICS26Envelope::ICS2Msg(client_msg_a));
            assert!(dispatch_res_a.is_ok());
            ctx_a.set_routing_context(routing_context_a);

            // Check if the update in the other direction succeeded.
            let client_height_a = ctx_a
                .query_client_full_state(&client_on_a_for_b)
                .unwrap()
                .latest_height();

            assert_eq!(client_height_a, ctx_b.query_latest_height());

            // Advance height for chain A.
            ctx_a.advance_chain_height();
        }

        // let msg = create_client_update(dest_chain_ctx);
        //
        // let res = update_client_to_latest(&mut ctx_ibc1, &ctx_a, &client_on_b_for_a);
    }
}
