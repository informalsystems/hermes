use std::convert::TryFrom;
use std::iter::FromIterator;
use std::str::FromStr;

use serde::Serialize;
use tendermint_proto::Protobuf;

use crate::ics03_connection::error::Kind;
use crate::ics24_host::identifier::ConnectionId;

//TODO: This might need to be migrated to ibc-proto crate. But ClientConnections (as array of strings)
// might not be part of an official proto file
#[derive(::prost::Message)]
pub struct RawClientConnections {
    #[prost(string, repeated, tag = "1")]
    pub connections: ::std::vec::Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ConnectionIds(pub Vec<ConnectionId>);

impl Protobuf<RawClientConnections> for ConnectionIds {}

impl TryFrom<RawClientConnections> for ConnectionIds {
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawClientConnections) -> Result<Self, Self::Error> {
        let mut connections: Vec<ConnectionId> = vec![];
        for value in value.connections {
            let conn_id = ConnectionId::from_str(&value.replace("connections/", ""));
            match conn_id {
                Ok(c) => connections.push(c),
                Err(_e) => return Err(Kind::IdentifierError.into()),
            }
        }
        Ok(ConnectionIds(connections))
    }
}

impl From<ConnectionIds> for RawClientConnections {
    fn from(value: ConnectionIds) -> Self {
        RawClientConnections {
            connections: value.0.iter().map(|v| v.to_string()).collect(),
        }
    }
}

impl FromIterator<ConnectionId> for ConnectionIds {
    fn from_iter<T: IntoIterator<Item = ConnectionId>>(iter: T) -> Self {
        let mut col = ConnectionIds(vec![]);

        for id in iter {
            col.0.push(id)
        }

        col
    }
}
