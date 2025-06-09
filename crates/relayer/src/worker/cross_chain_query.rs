use super::error::RunError;
use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    CrossChainQueryRequest, IncludeProof, QueryConnectionRequest, QueryHeight,
};
use crate::chain::tracking::TrackedMsgs;
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::foreign_client::ForeignClient;
use crate::object::CrossChainQuery;
use crate::telemetry;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::WorkerCmd;

use crossbeam_channel::Receiver;
use ibc_relayer_types::core::ics02_client::height::Height;
use std::time::Duration;
use tracing::{info, info_span};
use uuid::Uuid;

impl TryFrom<&IbcEventWithHeight> for CrossChainQueryRequest {
    type Error = Error;

    fn try_from(ibc_event_with_height: &IbcEventWithHeight) -> Result<Self, Self::Error> {
        match ibc_event_with_height.event.cross_chain_query_packet() {
            Some(packet) => Ok(CrossChainQueryRequest {
                chain_id: packet.chain_id.clone(),
                query_id: packet.query_id.to_string(),
                query_type: packet.query_type.clone(),
                request: packet.request.clone(),
                height: packet.height,
            }),
            None => Err(Error::ics31(
                ibc_relayer_types::applications::ics31_icq::error::Error::parse(),
            )),
        }
    }
}

pub fn spawn_cross_chain_query_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a_handle: ChainA,
    chain_b_handle: ChainB,
    cmd_rx: Receiver<WorkerCmd>,
    cross_chain_query: CrossChainQuery,
) -> TaskHandle {
    spawn_background_task(
        info_span!("cross chain query"),
        Some(Duration::from_millis(1000)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                handle_cross_chain_query(
                    chain_a_handle.clone(),
                    chain_b_handle.clone(),
                    cmd,
                    &cross_chain_query,
                )?;
            }
            Ok(Next::Continue)
        },
    )
}

fn handle_cross_chain_query<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a_handle: ChainA,
    chain_b_handle: ChainB,
    cmd: WorkerCmd,
    cross_chain_query: &CrossChainQuery,
) -> Result<(), TaskError<RunError>> {
    if let WorkerCmd::IbcEvents { batch } = &cmd {
        let queries: Vec<CrossChainQueryRequest> = batch
            .events
            .iter()
            .filter_map(|ev| ev.try_into().ok())
            .collect();

        // Handle of queried chain has to query data from it's RPC
        info!("request: {}", cross_chain_query.short_name());
        telemetry!(
            cross_chain_queries,
            &cross_chain_query.src_chain_id,
            &cross_chain_query.dst_chain_id,
            queries.len()
        );
        let response = chain_b_handle.cross_chain_query(queries);
        if let Ok(cross_chain_query_responses) = response {
            // Run only when cross chain query response is not empty
            if !cross_chain_query_responses.is_empty() {
                // Find connection between querying chain and queried chain
                let connection_end = chain_a_handle
                    .query_connection(
                        QueryConnectionRequest {
                            connection_id: cross_chain_query.connection_id.clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(|e| TaskError::Fatal(RunError::relayer(e).into()))?
                    .0;

                // Retrieve client based on client id
                let client_a = ForeignClient::find(
                    chain_b_handle.clone(),
                    chain_a_handle.clone(),
                    connection_end.client_id(),
                )
                .map_err(|e| TaskError::Fatal(RunError::foreign_client(e).into()))?;

                let target_height = Height::new(
                    chain_b_handle.id().version(),
                    cross_chain_query_responses.first().unwrap().height as u64,
                )
                .map_err(|e| TaskError::Fatal(RunError::ics02(e).into()))?
                .increment();

                // Push update client msg
                let mut chain_a_msgs = client_a
                    .wait_and_build_update_client(target_height)
                    .map_err(|e| TaskError::Fatal(RunError::foreign_client(e).into()))?;

                let num_cross_chain_query_responses = cross_chain_query_responses.len();

                for response in cross_chain_query_responses {
                    info!("response arrived: query_id: {}", response.query_id);
                    // After updating client, send response tx to querying chain
                    chain_a_msgs.push(
                        response
                            .try_to_any(
                                chain_a_handle
                                    .get_signer()
                                    .map_err(|e| TaskError::Fatal(RunError::relayer(e).into()))?,
                            )
                            .map_err(|e| TaskError::Fatal(RunError::ics31(e).into()))?,
                    );
                }

                let ccq_responses = chain_a_handle
                    .send_messages_and_wait_check_tx(TrackedMsgs::new_uuid(
                        chain_a_msgs,
                        Uuid::new_v4(),
                    ))
                    .map_err(|e| {
                        // Since all the CCQs failed, generate a failure code for the telemetry
                        let failed_codes =
                            vec![tendermint::abci::Code::from(1); num_cross_chain_query_responses];
                        telemetry!(
                            cross_chain_query_responses,
                            &cross_chain_query.dst_chain_id,
                            &cross_chain_query.src_chain_id,
                            failed_codes
                        );

                        TaskError::Ignore(RunError::relayer(e).into())
                    })?;

                telemetry!(
                    cross_chain_query_responses,
                    &cross_chain_query.dst_chain_id,
                    &cross_chain_query.src_chain_id,
                    ccq_responses
                        .iter()
                        .map(|ccq_response| ccq_response.code)
                        .collect()
                );
            }
        }
    }
    Ok(())
}
