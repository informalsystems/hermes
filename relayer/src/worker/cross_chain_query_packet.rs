use super::error::RunError;
use crate::chain::handle::ChainHandle;
use crate::util::task::{spawn_background_task, Next, TaskError, TaskHandle};
use crate::worker::WorkerCmd;
use crossbeam_channel::Receiver;
use std::time::Duration;
use tracing::info_span;
use crate::object::CrossChainQueryPacket;

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
        let queries = batch.events
            .iter()
            .filter_map(|ev| ev.try_into().ok())
            .collect();

        let res = handle.cross_chain_query(queries);
        println!("{:?}", res);
        Ok(())
    } else {
        Ok(())
    }
}
