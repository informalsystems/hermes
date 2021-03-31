use std::{ops::Deref, sync::Arc, thread};

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};
use crossbeam_channel as channel;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{config::ChainConfig, event::monitor::*};

use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct ListenCmd {
    #[options(free)]
    chain_id: Option<ChainId>,
}

impl ListenCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let rt = Arc::new(TokioRuntime::new()?);
        let config = app_config();

        let chain_id = self.chain_id.clone().unwrap();
        let chain_config = config.find_chain(&chain_id).unwrap();

        listen(rt, chain_config.clone())
    }
}

impl Runnable for ListenCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
    }
}

/// Listen to events
pub fn listen(rt: Arc<TokioRuntime>, config: ChainConfig) -> Result<(), BoxError> {
    info!(chain.id = %config.id, "spawning event monitor for");

    let (event_monitor, rx) = subscribe(config, rt)?;
    let _ = thread::spawn(|| event_monitor.run());

    while let Ok(event_batch) = rx.recv() {
        dbg!(event_batch);
    }

    Ok(())
}

fn subscribe(
    chain_config: ChainConfig,
    rt: Arc<TokioRuntime>,
) -> Result<(EventMonitor, channel::Receiver<EventBatch>), BoxError> {
    let (mut event_monitor, rx) =
        EventMonitor::new(chain_config.id, chain_config.websocket_addr, rt)
            .map_err(|e| format!("couldn't initialize event monitor: {}", e))?;

    event_monitor
        .subscribe()
        .map_err(|e| format!("couldn't initialize subscriptions: {}", e))?;

    Ok((event_monitor, rx))
}
