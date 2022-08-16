//! Module to provide caching support for the relayer.
//!
//! Utilizes the [`moka`](https://docs.rs/moka) crate, which provides full
//! concurrency of retrievals and a high expected concurrency for updates.
use core::fmt::Formatter;
use std::fmt;
use std::time::Duration;

use moka::sync::Cache as MokaCache;

use ibc::core::ics02_client::height::Height;
use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::ChannelEnd;
use ibc::core::ics24_host::identifier::{ClientId, ConnectionId, PortChannelId};

use crate::client_state::AnyClientState;

const CHANNEL_CACHE_TTL: Duration = Duration::from_secs(60);
const CONNECTION_CACHE_TTL: Duration = Duration::from_secs(10 * 60);
const CLIENT_STATE_CACHE_TTL: Duration = Duration::from_millis(500);
const LATEST_HEIGHT_CACHE_TTL: Duration = Duration::from_millis(200);

const CHANNEL_CACHE_CAPACITY: u64 = 10_000;
const CONNECTION_CACHE_CAPACITY: u64 = 10_000;
const CLIENT_STATE_CACHE_CAPACITY: u64 = 10_000;

/// Whether or not a result was in cache (ie. a cache hit)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CacheStatus {
    Hit,
    Miss,
}

/// Alias for a result and its cache status.
pub type CacheResult<A, E> = Result<(A, CacheStatus), E>;

/// The main cache data structure, which comprises multiple sub-caches for caching
/// different chain components, each with different time-to-live values.
///
/// There should be one `Cache` instantiated per every chain runtime.
#[derive(Clone)]
pub struct Cache {
    /// Cache storing [`ChannelEnd`]s keyed by their [`PortChannelId`]s.
    channels: MokaCache<PortChannelId, ChannelEnd>,
    /// Cache storing [`ConnectionEnd`]s keyed by their [`ConnectionId`]s.
    connections: MokaCache<ConnectionId, ConnectionEnd>,
    /// Cache storing [`AnyClientState`]s keyed by their [`ClientId`]s.
    client_states: MokaCache<ClientId, AnyClientState>,
    /// The latest `Height` associated with the chain runtime this `Cache` is associated with.
    latest_height: MokaCache<(), Height>,
}

impl Default for Cache {
    fn default() -> Self {
        Self::new()
    }
}

impl Cache {
    /// Initializes a new empty [`Cache`] with default time-to-live values.
    pub fn new() -> Cache {
        let channels = MokaCache::builder()
            .time_to_live(CHANNEL_CACHE_TTL)
            .max_capacity(CHANNEL_CACHE_CAPACITY)
            .build();

        let connections = MokaCache::builder()
            .time_to_live(CONNECTION_CACHE_TTL)
            .max_capacity(CONNECTION_CACHE_CAPACITY)
            .build();

        let client_states = MokaCache::builder()
            .time_to_live(CLIENT_STATE_CACHE_TTL)
            .max_capacity(CLIENT_STATE_CACHE_CAPACITY)
            .build();

        let latest_height = MokaCache::builder()
            .time_to_live(LATEST_HEIGHT_CACHE_TTL)
            .max_capacity(1)
            .build();

        Cache {
            channels,
            connections,
            client_states,
            latest_height,
        }
    }

    /// Return a cached [`ChannelEnd`] via its [`PortChannelId`] if it exists in the cache.
    /// Otherwise, attempts to fetch it via the supplied fetcher function `F`. If `F`
    /// returns successfully with the channel end in an open state, a copy of it is stored in
    /// the cache before it is returned.
    pub fn get_or_try_insert_channel_with<F, E>(
        &self,
        id: &PortChannelId,
        f: F,
    ) -> CacheResult<ChannelEnd, E>
    where
        F: FnOnce() -> Result<ChannelEnd, E>,
    {
        if let Some(chan) = self.channels.get(id) {
            // If cache hit, return it.
            Ok((chan, CacheStatus::Hit))
        } else {
            // Only cache a channel end if the channel is open.
            let chan = f()?;
            if chan.state().is_open() {
                self.channels.insert(id.clone(), chan.clone());
            }
            Ok((chan, CacheStatus::Miss))
        }
    }

    /// Return a cached [`ConnectionEnd`] via its [`ConnectionId`] if it exists in the cache.
    /// Otherwise, attempts to fetch it via the supplied fetcher function `F`. If `F`
    /// returns successfully with the connection end in an open state, a copy of it is
    /// in the cache before it is returned.
    pub fn get_or_try_insert_connection_with<F, E>(
        &self,
        id: &ConnectionId,
        f: F,
    ) -> CacheResult<ConnectionEnd, E>
    where
        F: FnOnce() -> Result<ConnectionEnd, E>,
    {
        if let Some(conn) = self.connections.get(id) {
            Ok((conn, CacheStatus::Hit))
        } else {
            let conn = f()?;
            if conn.state().is_open() {
                self.connections.insert(id.clone(), conn.clone());
            }
            Ok((conn, CacheStatus::Miss))
        }
    }

    /// Return a cached [`AnyClientState`] via its [`ClientId`] if it exists in the cache.
    /// Otherwise, attempts to fetch it via the supplied fetcher function `F`. If `F`
    /// returns successfully with the client state, a copy of it is stored in the cache
    /// before it is returned.
    pub fn get_or_try_insert_client_state_with<F, E>(
        &self,
        id: &ClientId,
        f: F,
    ) -> CacheResult<AnyClientState, E>
    where
        F: FnOnce() -> Result<AnyClientState, E>,
    {
        if let Some(state) = self.client_states.get(id) {
            Ok((state, CacheStatus::Hit))
        } else {
            let state = f()?;
            self.client_states.insert(id.clone(), state.clone());
            Ok((state, CacheStatus::Miss))
        }
    }

    /// Returns the latest [`Height`] value if it exists in the cache.
    /// Otherwise, attempts to fetch it via the supplied fetcher function `F`. If
    /// `F` returns successfully with the latest height, a copy of it is stored in the
    /// cache before it is returned.
    ///
    /// This value is cached with a small time-to-live so that the latest height
    /// query returns the same height if the same query is repeated within a small time frame.
    pub fn get_or_try_update_latest_height_with<F, E>(&self, f: F) -> CacheResult<Height, E>
    where
        F: FnOnce() -> Result<Height, E>,
    {
        if let Some(height) = self.latest_height.get(&()) {
            Ok((height, CacheStatus::Hit))
        } else {
            let height = f()?;
            self.latest_height.insert((), height);
            Ok((height, CacheStatus::Miss))
        }
    }
}

impl fmt::Debug for Cache {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Cache").finish_non_exhaustive()
    }
}
