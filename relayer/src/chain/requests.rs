use ibc_proto::ibc::core::channel::v1::QueryChannelClientStateRequest as RawQueryChannelClientStateRequest;

use crate::error::Error;
use serde::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QueryChannelClientStateRequest {
    pub port_id: String,
    pub channel_id: String,
}

impl Protobuf<RawQueryChannelClientStateRequest> for QueryChannelClientStateRequest {}

impl TryFrom<RawQueryChannelClientStateRequest> for QueryChannelClientStateRequest {
    type Error = Error;

    fn try_from(raw_request: RawQueryChannelClientStateRequest) -> Result<Self, Self::Error> {
        Ok(QueryChannelClientStateRequest {
            port_id: raw_request.port_id,
            channel_id: raw_request.channel_id,
        })
    }
}

impl From<QueryChannelClientStateRequest> for RawQueryChannelClientStateRequest {
    fn from(request: QueryChannelClientStateRequest) -> Self {
        RawQueryChannelClientStateRequest {
            port_id: request.port_id,
            channel_id: request.channel_id,
        }
    }
}
