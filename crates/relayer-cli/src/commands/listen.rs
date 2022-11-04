use alloc::sync::Arc;
use core::{
    fmt::{Display, Error as FmtError, Formatter},
    ops::Deref,
    str::FromStr,
};
use std::thread;

use abscissa_core::clap::Parser;
use abscissa_core::{application::fatal_error, Runnable};
use itertools::Itertools;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::{error, info, instrument};

use ibc_relayer_types::{core::ics24_host::identifier::ChainId, events::IbcEvent};

use eyre::eyre;
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
            EventFilter::Tx => !(matches!(event, IbcEvent::NewBlock(_) | IbcEvent::ChainError(_))),
        }
    }
}

impl Display for EventFilter {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
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

#[derive(Debug, Parser, PartialEq, Eq)]
pub struct ListenCmd {
    /// Identifier of the chain to listen for events from
    #[clap(
        long = "chain",
        required = true,
        help_heading = "REQUIRED",
        value_name = "CHAIN_ID"
    )]
    chain_id: ChainId,

    /// Add an event type to listen for, can be repeated.
    /// Listen for all events by default (available: Tx, NewBlock).
    #[clap(long = "events", value_name = "EVENT", multiple_values = true)]
    events: Vec<EventFilter>,
}

impl ListenCmd {
    fn cmd(&self) -> eyre::Result<()> {
        let config = app_config();

        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| eyre!("chain '{}' not found in configuration", self.chain_id))?;

        let events = if self.events.is_empty() {
            &[EventFilter::Tx, EventFilter::NewBlock]
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

#[instrument(skip_all, level = "error", fields(chain = %config.id))]
pub fn listen(config: &ChainConfig, filters: &[EventFilter]) -> eyre::Result<()> {
    let rt = Arc::new(TokioRuntime::new()?);
    let (event_monitor, rx) = subscribe(config, rt)?;

    info!(
        "listening for queries: {}",
        event_monitor.queries().iter().format(", "),
    );

    thread::spawn(|| event_monitor.run());

    while let Ok(event_batch) = rx.recv() {
        match event_batch {
            Ok(batch) => {
                let _span =
                    tracing::error_span!("event_batch", batch_height = %batch.height).entered();

                let matching_events = batch
                    .events
                    .into_iter()
                    .filter(|e| event_match(&e.event, filters))
                    .collect_vec();

                if matching_events.is_empty() {
                    continue;
                }

                for event in matching_events {
                    info!("{}", event);
                }
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
) -> eyre::Result<(EventMonitor, EventReceiver)> {
    let (mut event_monitor, rx, _) = EventMonitor::new(
        chain_config.id.clone(),
        chain_config.websocket_addr.clone(),
        rt,
    )
    .map_err(|e| eyre!("could not initialize event monitor: {}", e))?;

    event_monitor
        .subscribe()
        .map_err(|e| eyre!("could not initialize subscriptions: {}", e))?;

    Ok((event_monitor, rx))
}

#[cfg(test)]
mod tests {
    use super::{EventFilter, ListenCmd};

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_listen_required_only() {
        assert_eq!(
            ListenCmd {
                chain_id: ChainId::from_string("chain_id"),
                events: vec!()
            },
            ListenCmd::parse_from(["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_listen_single_event() {
        assert_eq!(
            ListenCmd {
                chain_id: ChainId::from_string("chain_id"),
                events: vec!(EventFilter::from_str("Tx").unwrap())
            },
            ListenCmd::parse_from(["test", "--chain", "chain_id", "--events", "Tx"])
        )
    }

    #[test]
    fn test_listen_multiple_events() {
        assert_eq!(
            ListenCmd {
                chain_id: ChainId::from_string("chain_id"),
                events: vec!(
                    EventFilter::from_str("Tx").unwrap(),
                    EventFilter::from_str("NewBlock").unwrap()
                )
            },
            ListenCmd::parse_from([
                "test", "--chain", "chain_id", "--events", "Tx", "--events", "NewBlock"
            ])
        )
    }

    #[test]
    fn test_listen_multiple_events_single_flag() {
        assert_eq!(
            ListenCmd {
                chain_id: ChainId::from_string("chain_id"),
                events: vec!(
                    EventFilter::from_str("Tx").unwrap(),
                    EventFilter::from_str("NewBlock").unwrap()
                )
            },
            ListenCmd::parse_from(["test", "--chain", "chain_id", "--events", "Tx", "NewBlock"])
        )
    }

    #[test]
    fn test_listen_unknown_event_filter() {
        assert!(ListenCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--events",
            "TestFilter"
        ])
        .is_err())
    }

    #[test]
    fn test_listen_unknown_no_chain() {
        assert!(ListenCmd::try_parse_from(["test"]).is_err())
    }
}
