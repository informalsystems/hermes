use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::QueryChannelClientStateRequest as RawQueryChannelClientStateRequest;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QueryChannelClientStateRequest {
    pub port_id: String,
    pub channel_id: String,
}

impl From<QueryChannelClientStateRequest> for RawQueryChannelClientStateRequest {
    fn from(request: QueryChannelClientStateRequest) -> Self {
        RawQueryChannelClientStateRequest {
            port_id: request.port_id,
            channel_id: request.channel_id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QueryChannelRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub height: Height,
}
