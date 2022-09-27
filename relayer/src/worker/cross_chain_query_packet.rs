use super::error::RunError;
use crate::chain::handle::ChainHandle;
use crate::object::CrossChainQueryPacket;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::WorkerCmd;
use crossbeam_channel::Receiver;
use std::time::Duration;
use tracing::info_span;

pub fn spawn_cross_chain_query_packet_worker<ChainA: ChainHandle>(
    handle: ChainA,
    cmd_rx: Receiver<WorkerCmd>,
    cross_chain_query_packet: CrossChainQueryPacket,
) -> TaskHandle {
    spawn_background_task(
        info_span!("cross_chain_query"),
        Some(Duration::from_millis(1000)),
        move || {
            if let Ok(cmd) = cmd_rx.try_recv() {
                handle_cross_chain_query_packet(handle.clone(), cmd, &cross_chain_query_packet)?;
            }
            Ok(Next::Continue)
        },
    )
}

fn handle_cross_chain_query_packet<ChainA: ChainHandle>(
    handle: ChainA,
    cmd: WorkerCmd,
    _cross_chain_query_packet: &CrossChainQueryPacket,
) -> Result<(), TaskError<RunError>> {
    if let WorkerCmd::IbcEvents { batch } = &cmd {
        let queries = batch
            .events
            .iter()
            .filter_map(|ev| ev.try_into().ok())
            .collect();

        // TODO: send async tx to src chain in order to store query results
        // TODO: encode tx message into proto message
        let response = handle.cross_chain_query(queries);
        if let Ok(res) = response {
            for i in res {
                println!("{}", i);
            }
        }

        let key = handle.get_key().unwrap();
        println!("{:?}", key);

        Ok(())
    } else {
        Ok(())
    }
}
