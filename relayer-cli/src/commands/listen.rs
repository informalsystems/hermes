use alloc::sync::Arc;
use core::{fmt, ops::Deref, str::FromStr};
use std::thread;

use abscissa_core::{application::fatal_error, Runnable};
use clap::{App, Arg, ArgMatches, Args, FromArgMatches};
use itertools::Itertools;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::{error, info};

use ibc::{core::ics24_host::identifier::ChainId, events::IbcEvent};

use ibc_relayer::{
    config::ChainConfig,
    event::monitor::{EventMonitor, EventReceiver},
};

use crate::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EventFilter {
    NewBlock,
    Tx,
}

impl EventFilter {
    pub fn matches(&self, event: &IbcEvent) -> bool {
        match self {
            EventFilter::NewBlock => matches!(event, IbcEvent::NewBlock(_)),
            EventFilter::Tx => {
                !(matches!(
                    event,
                    IbcEvent::NewBlock(_) | IbcEvent::Empty(_) | IbcEvent::ChainError(_)
                ))
            }
        }
    }
}

impl fmt::Display for EventFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NewBlock => write!(f, "NewBlock"),
            Self::Tx => write!(f, "Tx"),
        }
    }
}

impl FromStr for EventFilter {
    type Err = Box<dyn std::error::Error + Send + Sync + 'static>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "NewBlock" => Ok(Self::NewBlock),
            "Tx" => Ok(Self::Tx),
            invalid => Err(format!("unrecognized event type: {}", invalid).into()),
        }
    }
}

#[derive(Debug)]
pub struct ListenCmd {
    /// Identifier of the chain to listen for events from
    chain_id: ChainId,

    /// Event types to listen for
    events: Vec<EventFilter>,
}

impl ListenCmd {
    fn cmd(&self) -> Result<(), Box<dyn std::error::Error>> {
        let config = app_config();

        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration", self.chain_id))?;

        let events = if self.events.is_empty() {
            &[EventFilter::Tx, EventFilter::NewBlock]
        } else {
            self.events.as_slice()
        };

        listen(chain_config, events)
    }
}

// Can't derive Clap: a Vec struct field is translated by clap_derive to an
// arg with multiple_values(true), not multiple_occurrences(true).
// Implement all the necessary traits manually instead.
// See https://github.com/clap-rs/clap/issues/1772

impl Args for ListenCmd {
    fn augment_args(app: App<'_>) -> App<'_> {
        augment_args(app, true)
    }

    fn augment_args_for_update(app: App<'_>) -> App<'_> {
        augment_args(app, false)
    }
}

fn augment_args(app: App<'_>, required: bool) -> App<'_> {
    app.arg(
        Arg::new("chain_id")
            .required(required)
            .about("Identifier of the chain to listen for events from")
            .validator(ChainId::from_str),
    )
    .arg(
        Arg::new("events")
            .multiple_occurrences(true)
            .short('e')
            .long("event")
            .value_name("EVENT")
            .about(
                "Add an event type to listen for, can be repeated.\n\
                Listen for all events by default (available: Tx, NewBlock)",
            )
            .validator(EventFilter::from_str),
    )
}

impl FromArgMatches for ListenCmd {
    fn from_arg_matches(matches: &ArgMatches) -> Option<Self> {
        let chain_id = parse_chain_id(matches).expect("the required argument should be present");
        let events = parse_event_filters(matches).unwrap_or_default();
        Some(ListenCmd { chain_id, events })
    }

    fn update_from_arg_matches(&mut self, matches: &ArgMatches) {
        if let Some(chain_id) = parse_chain_id(matches) {
            self.chain_id = chain_id;
        }
        if let Some(events) = parse_event_filters(matches) {
            self.events = events;
        }
    }
}

fn parse_chain_id(matches: &ArgMatches) -> Option<ChainId> {
    let val = matches.value_of("chain_id")?;
    Some(ChainId::from_str(val).unwrap())
}

fn parse_event_filters(matches: &ArgMatches) -> Option<Vec<EventFilter>> {
    let vals = matches.values_of("events")?;
    Some(vals.map(|s| EventFilter::from_str(s).unwrap()).collect())
}

impl Runnable for ListenCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
    }
}

/// Listen to events
pub fn listen(
    config: &ChainConfig,
    filters: &[EventFilter],
) -> Result<(), Box<dyn std::error::Error>> {
    let rt = Arc::new(TokioRuntime::new()?);
    let (event_monitor, rx) = subscribe(config, rt)?;

    info!(
        "[{}] listening for queries {}",
        config.id,
        event_monitor.queries().iter().format(", "),
    );

    thread::spawn(|| event_monitor.run());

    while let Ok(event_batch) = rx.recv() {
        match event_batch {
            Ok(batch) => {
                let matching_events = batch
                    .events
                    .into_iter()
                    .filter(|e| event_match(e, filters))
                    .collect_vec();

                if matching_events.is_empty() {
                    continue;
                }

                info!("- event batch at height {}", batch.height);

                for event in matching_events {
                    info!("+ {:#?}", event);
                }

                info!("");
            }
            Err(e) => error!("- error: {}", e),
        }
    }

    Ok(())
}

fn event_match(event: &IbcEvent, filters: &[EventFilter]) -> bool {
    filters.iter().any(|f| f.matches(event))
}

fn subscribe(
    chain_config: &ChainConfig,
    rt: Arc<TokioRuntime>,
) -> Result<(EventMonitor, EventReceiver), Box<dyn std::error::Error>> {
    let (mut event_monitor, rx, _) = EventMonitor::new(
        chain_config.id.clone(),
        chain_config.websocket_addr.clone(),
        rt,
    )
    .map_err(|e| format!("could not initialize event monitor: {}", e))?;

    event_monitor
        .subscribe()
        .map_err(|e| format!("could not initialize subscriptions: {}", e))?;

    Ok((event_monitor, rx))
}
