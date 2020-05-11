use std::fmt;

use crate::ics24_host::identifier::{ChannelId, ClientId, PortId};
use crate::Height;

mod cosmos;
mod ics;

#[cfg(feature = "paths-cosmos")]
use cosmos as paths;
#[cfg(not(feature = "paths-cosmos"))]
use ics as paths;

pub struct Key<'a, P>(&'a P);

impl<'a, P> fmt::Display for Key<'a, P>
where
    P: Path,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.to_string())
    }
}

impl<'a, P> Into<Vec<u8>> for Key<'a, P>
where
    P: Path,
{
    fn into(self) -> Vec<u8> {
        self.to_string().into_bytes()
    }
}

pub trait Path: Sized {
    fn to_string(&self) -> String;

    fn to_key(&self) -> Key<'_, Self> {
        Key(self)
    }
}

pub struct ConnectionPath {
    pub connection_id: String,
}

impl Path for ConnectionPath {
    fn to_string(&self) -> String {
        paths::connection_path(&self)
    }
}

pub struct ConsensusStatePath {
    pub client_id: ClientId,
    pub height: Height,
}

impl ConsensusStatePath {
    pub fn new(client_id: ClientId, height: Height) -> Self {
        Self { client_id, height }
    }
}

impl Path for ConsensusStatePath {
    fn to_string(&self) -> String {
        paths::consensus_state_path(&self)
    }
}

pub struct ClientStatePath {
    pub client_id: ClientId,
}

impl ClientStatePath {
    pub fn new(client_id: ClientId) -> Self {
        Self { client_id }
    }
}

impl Path for ClientStatePath {
    fn to_string(&self) -> String {
        paths::client_state_path(&self)
    }
}

pub struct ChannelPath {
    pub port_id: PortId,
    channel_id: ChannelId,
}

impl ChannelPath {
    pub fn new(port_id: PortId, channel_id: ChannelId) -> Self {
        Self {
            port_id,
            channel_id,
        }
    }
}

const KEY_CHANNEL_PREFIX: &str = "channelEnds";

pub type ChannelEndsPath = ChannelPath;

impl Path for ChannelEndsPath {
    fn to_string(&self) -> String {
        format!("{}/{}", KEY_CHANNEL_PREFIX, paths::channel_path(&self))
    }
}
