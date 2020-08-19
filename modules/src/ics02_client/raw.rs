use crate::ics03_connection::error::Kind;
use crate::ics24_host::identifier::ConnectionId;
use crate::try_from_raw::TryFromRaw;
use std::str::FromStr;

//TODO: This might need to be migrated to ibc-proto crate. But ClientConnections (as array of strings)
// might not be part of an official proto file
#[derive(::prost::Message)]
pub struct RawClientConnections {
    #[prost(string, repeated, tag = "1")]
    pub connections: ::std::vec::Vec<String>,
}

impl TryFromRaw for Vec<ConnectionId> {
    type RawType = RawClientConnections;
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawClientConnections) -> Result<Self, Self::Error> {
        if !value.connections.is_empty() {
            let mut connections: Vec<ConnectionId> = vec![];
            for value in value.connections {
                let conn_id = ConnectionId::from_str(&value.replace("connections/", ""));
                match conn_id {
                    Ok(c) => connections.push(c),
                    Err(_e) => return Err(Kind::IdentifierError.into()),
                }
            }
            Ok(connections)
        } else {
            Err(Kind::ConnectionNotFound.into())
        }
    }
}
