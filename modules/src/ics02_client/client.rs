use crate::ics03_connection::error::Kind;
use crate::try_from_raw::TryFromRaw;

//TODO: This might need to be migrated to ibc-proto crate. But ClientConnections (as array of strings)
// might not be part of an official proto file
#[derive(::prost::Message)]
pub struct RawClientConnections {
    #[prost(string, repeated, tag = "1")]
    pub connections: ::std::vec::Vec<String>,
}

impl TryFromRaw for Vec<String> {
    type RawType = RawClientConnections;
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawClientConnections) -> Result<Self, Self::Error> {
        if !value.connections.is_empty() {
            Ok(value.connections)
        } else {
            Err(Kind::ConnectionNotFound.into())
        }
    }
}
