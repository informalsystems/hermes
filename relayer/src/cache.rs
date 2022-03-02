#![allow(unused_variables, dead_code)]
// TODO: Remove hacky allow pragmas

use core::fmt::Formatter;
use std::fmt;
use std::time::Duration;

use moka::sync;

use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::ChannelEnd;
use ibc::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};

#[derive(Clone)]
pub struct Cache {
    channels: sync::Cache<(PortId, ChannelId), ChannelEnd>,
    connections: sync::Cache<ConnectionId, ConnectionEnd>,
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

    pub fn get_or_try_insert_channel_with<F, E>(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        f: F,
    ) -> Result<ChannelEnd, E>
    where
        F: FnOnce() -> Result<ChannelEnd, E>,
    {
        // FIXME: create a struct type for this
        let key = (port_id.clone(), channel_id.clone());
        if let Some(chan) = self.channels.get(&key) {
            Ok(chan)
        } else {
            let chan = f()?;
            if chan.state().is_open() {
                self.channels.insert(key, chan.clone());
            }
            Ok(chan)
        }
    }

    pub fn get_or_try_insert_connection_with<F, E>(
        &self,
        id: &ConnectionId,
        f: F,
    ) -> Result<ConnectionEnd, E>
    where
        F: FnOnce() -> Result<ConnectionEnd, E>,
    {
        if let Some(conn) = self.connections.get(id) {
            Ok(conn)
        } else {
            let conn = f()?;
            if conn.state().is_open() {
                self.connections.insert(id.clone(), conn.clone());
            }
            Ok(conn)
        }
    }
}

impl fmt::Debug for Cache {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Cache").finish_non_exhaustive()
    }
}
