use anomaly::fail;

use ::tendermint::lite::types as tmlite;
use ::tendermint::lite::{self, Height};
use ::tendermint::rpc::Client as RpcClient;

use relayer_modules::ics02_client::state::ConsensusState;

use crate::config::ChainConfig;
use crate::error;

pub mod tendermint;

pub trait Chain {
    type Type;
    type Header: tmlite::Header;
    type Commit: tmlite::Commit;
    type ConsensusState: ConsensusState;
    type Requester: tmlite::Requester<Self::Commit, Self::Header>;

    fn config(&self) -> &ChainConfig;
    fn rpc_client(&self) -> &RpcClient;
    fn requester(&self) -> &Self::Requester;
}

pub async fn query_latest_height(chain: &impl Chain) -> Result<Height, error::Error> {
    let status = chain
        .rpc_client()
        .status()
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    if status.sync_info.catching_up {
        fail!(
            error::Kind::LightClient,
            "node at {} running chain {} not caught up",
            chain.config().rpc_addr,
            chain.config().id,
        );
    }

    Ok(status.sync_info.latest_block_height.into())
}

pub async fn query_header_at_height<C>(
    chain: &C,
    height: Height,
) -> Result<lite::SignedHeader<C::Commit, C::Header>, error::Error>
where
    C: Chain,
{
    use tmlite::Requester;

    let header = chain
        .requester()
        .signed_header(height)
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    Ok(header)
}
