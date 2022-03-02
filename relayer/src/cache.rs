#![allow(unused_variables, dead_code)]
// TODO: Remove hacky allow pragmas

use core::fmt::Formatter;
use std::fmt;
use std::time::Duration;

use moka::sync;

use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::ChannelEnd;

use crate::supervisor::client_state_filter::CacheKey;

#[derive(Clone)]
pub struct Cache {
    channels: sync::Cache<CacheKey, ChannelEnd>,
    connections: sync::Cache<CacheKey, ConnectionEnd>,
}

impl Cache {
    pub fn new() -> Cache {
        // TODO: Module-level constants.
        // Time to live (TTL) and TIL: 10 minutes
        let chans = sync::Cache::builder()
            .time_to_live(Duration::from_secs(10 * 60))
            .time_to_idle(Duration::from_secs(10 * 60))
            .build();

        let conns = sync::Cache::builder()
            .time_to_live(Duration::from_secs(10 * 60))
            .time_to_idle(Duration::from_secs(10 * 60))
            .build();

        Cache {
            channels: chans,
            connections: conns,
        }
    }
}

impl fmt::Debug for Cache {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}
