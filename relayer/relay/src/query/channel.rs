use relayer_modules::ics24_host::identifier::{ChannelId, PortId};
use relayer_modules::Height;

use super::ibc_query;
use crate::chain::Chain;
use relayer_modules::ics04_channel::query::{ChannelResponse, QueryChannel};

use relayer_modules::error;

pub async fn query_channel<C>(
    chain: &C,
    chain_height: Height,
    port_id: PortId,
    channel_id: ChannelId,
    prove: bool,
) -> Result<ChannelResponse, error::Error>
where
    C: Chain,
{
    let query = QueryChannel::new(chain_height, port_id, channel_id, prove);
    ibc_query(chain, query).await
}
