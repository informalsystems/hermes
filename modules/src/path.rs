use std::fmt;

use crate::ics24_host::client::ClientId;
use crate::Height;

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
        format!("connection/{}", self.connection_id)
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
        format!("consensusState/{}/{}", self.client_id, self.height)
    }
}
