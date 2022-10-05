use super::error::RunError;
use crate::chain::handle::ChainHandle;
use crate::chain::tracking::TrackedMsgs;
use crate::object::CrossChainQueryPacket;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::WorkerCmd;
use crossbeam_channel::Receiver;
use std::time::Duration;
use tracing::info_span;
use uuid::Uuid;
use crate::chain::requests::CrossChainQueryRequest;

pub fn spawn_cross_chain_query_packet_worker<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: ChainA,
    handle_b: ChainB,
    cmd_rx: Receiver<WorkerCmd>,
    cross_chain_query_packet: CrossChainQueryPacket,
) -> TaskHandle {
    spawn_background_task(
        info_span!("cross_chain_query"),
        Some(Duration::from_millis(1000)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                handle_cross_chain_query_packet(handle_a.clone(), handle_b.clone(), cmd, &cross_chain_query_packet)?;
            }
            Ok(Next::Continue)
        },
    )
}

fn append_rest_endpoint(
    mut req: CrossChainQueryRequest,
    endpoint: String,
) -> CrossChainQueryRequest {
    let path = String::from_utf8_lossy(&hex::decode(req.path).unwrap()).to_string();
    let raw_path = hex::encode(format!("{}{}", endpoint, path));
    println!("{}", endpoint);
    println!("{}", path);
    println!("{}", raw_path);
    req.path = raw_path;
    req
}

fn handle_cross_chain_query_packet<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: ChainA,
    handle_b: ChainB,
    cmd: WorkerCmd,
    _cross_chain_query_packet: &CrossChainQueryPacket,
) -> Result<(), TaskError<RunError>> {
    if let WorkerCmd::IbcEvents { batch } = &cmd {
        let mut chain_a_queries: Vec<CrossChainQueryRequest> = vec![];
        let mut chain_b_queries: Vec<CrossChainQueryRequest> = vec![];

        let queries: Vec<CrossChainQueryRequest> = batch
            .events
            .iter()
            .filter_map(|ev| ev.try_into().ok())
            .collect();


        for query in queries {
            println!("{:?}", query);


            println!("{:?}", handle_a.config().unwrap());
            println!("{:?}", handle_b.config().unwrap());

            if handle_a.id().to_string() == query.chain_id.to_string() {
                chain_a_queries.push(append_rest_endpoint(query, handle_b.config().unwrap().rest_addr.to_string()));
            } else if handle_b.id().to_string() == query.chain_id.to_string() {
                chain_b_queries.push(append_rest_endpoint(query, handle_a.config().unwrap().rest_addr.to_string()));
            }
        }


        execute_cross_chain_query(handle_a, chain_a_queries)?;
        execute_cross_chain_query(handle_b, chain_b_queries)?;

        Ok(())
    } else {
        Ok(())
    }
}

fn execute_cross_chain_query<Handle: ChainHandle>(
    handle: Handle,
    queries: Vec<CrossChainQueryRequest>,
) -> Result<(), TaskError<RunError>> {
    let response = handle.cross_chain_query(queries);
    if let Ok(res) = response {
        let any_msgs = res.clone()
            .into_iter()
            .map(|r| r.to_any(&handle))
            .collect::<Vec<_>>();

        handle
            .send_messages_and_wait_check_tx(TrackedMsgs::new_uuid(any_msgs, Uuid::new_v4()))
            .map_err(|_| TaskError::Ignore(RunError::query()))?;
    }
    Ok(())
}

#[cfg(test)]
mod test_cross_chain_query_packet {
    use crate::chain::handle::BaseChainHandle;
    use crate::chain::mock::test_utils::get_basic_chain_config;
    use crate::chain::mock::MockChain;
    use crate::chain::runtime::ChainRuntime;
    use crate::chain::tracking::TrackingId;
    use crate::event::monitor::EventBatch;
    use crate::event::IbcEventWithHeight;
    use crate::object::CrossChainQueryPacket;
    use crate::worker::cross_chain_query_packet::spawn_cross_chain_query_packet_worker;
    use crate::worker::WorkerCmd;
    use crossbeam_channel;
    use ibc::applications::ics31_cross_chain_query::events::SendPacket;
    use ibc::core::ics02_client::height::Height;
    use ibc::core::ics24_host::identifier::ChainId;
    use ibc::events::IbcEvent;
    use std::sync::Arc;
    use tokio::runtime::Runtime as TokioRuntime;

    #[test]
    fn test() {
        let (tx, rx) = crossbeam_channel::unbounded();
        let a_cfg = get_basic_chain_config("chain_a");

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let query_rt = Arc::new(TokioRuntime::new().unwrap());
        let a_chain = ChainRuntime::<MockChain>::spawn::<BaseChainHandle>(
            a_cfg,
            rt.clone(),
            query_rt.clone(),
        )
            .unwrap();

        let worker_cmd = WorkerCmd::IbcEvents {
            batch: EventBatch {
                chain_id: Default::default(),
                tracking_id: TrackingId::new_uuid(),
                height: Height::new(1, 1).unwrap(),
                events: vec![IbcEventWithHeight {
                    event: IbcEvent::CrossChainQuery(SendPacket::new(
                        "1".into(),
                        "https://www.google.com/".into(),
                        "1".into(),
                    )),
                    height: Height::new(1, 1).unwrap(),
                }],
            },
        };

        tx.send(worker_cmd).unwrap();

        spawn_cross_chain_query_packet_worker(
            a_chain,
            b_chain,
            rx,
            CrossChainQueryPacket {
                src_chain_id: ChainId::new("chain_a".into(), 1),
                id: "1".to_string(),
            },
        )
            .join();
    }
}
