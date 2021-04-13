use std::{ops::Deref, sync::Arc, thread};

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};
use crossbeam_channel as channel;
use itertools::Itertools;
use tokio::runtime::Runtime as TokioRuntime;

use tendermint_rpc::query::{EventType, Query};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{config::ChainConfig, event::monitor::*};

use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct ListenCmd {
    /// Identifier of the chain to listen for events from
    #[options(free)]
    chain_id: ChainId,

    /// Add an event type to listen for, can be repeated. Listen for all events by default (available: Tx, NewBlock)
    #[options(short = "e", long = "event", meta = "EVENT")]
    events: Vec<EventType>,
}

impl ListenCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config();

        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration", self.chain_id))?;

        let events = if self.events.is_empty() {
            &[EventType::Tx, EventType::NewBlock]
        } else {
            self.events.as_slice()
        };

        listen(chain_config, events)
    }
}

impl Runnable for ListenCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
    }
}

/// Listen to events
pub fn listen(config: &ChainConfig, events: &[EventType]) -> Result<(), BoxError> {
    println!(
        "[info] Listening for events `{}` on '{}'...",
        events.iter().format(", "),
        config.id
    );

    let rt = Arc::new(TokioRuntime::new()?);
    let queries = events.iter().cloned().map(Query::from).collect();
    let (event_monitor, rx) = subscribe(&config, queries, rt)?;

    thread::spawn(|| event_monitor.run());

    while let Ok(event_batch) = rx.recv() {
        println!("{:#?}", event_batch);
    }

    Ok(())
}

fn subscribe(
    chain_config: &ChainConfig,
    queries: Vec<Query>,
    rt: Arc<TokioRuntime>,
) -> Result<(EventMonitor, channel::Receiver<EventBatch>), BoxError> {
    let (mut event_monitor, rx) = EventMonitor::new(
        chain_config.id.clone(),
        chain_config.websocket_addr.clone(),
        rt,
    )
    .map_err(|e| format!("could not initialize event monitor: {}", e))?;

    event_monitor.set_queries(queries);

    event_monitor
        .subscribe()
        .map_err(|e| format!("could not initialize subscriptions: {}", e))?;

    Ok((event_monitor, rx))
}
