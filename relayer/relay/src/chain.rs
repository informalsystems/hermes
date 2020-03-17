use std::time::Duration;

use anomaly::fail;
use serde::{de::DeserializeOwned, Serialize};

use ::tendermint::chain::Id as ChainId;
use ::tendermint::lite::types as tmlite;
use ::tendermint::lite::{self, Height, TrustThresholdFraction};
use ::tendermint::rpc::Client as RpcClient;

use relayer_modules::ics02_client::state::ConsensusState;

use crate::config::ChainConfig;
use crate::error;

pub mod tendermint;

pub type ValidatorSet<Chain> = <<Chain as self::Chain>::Commit as tmlite::Commit>::ValidatorSet;

pub trait Chain {
    type Header: tmlite::Header + Serialize + DeserializeOwned;
    type Commit: tmlite::Commit + Serialize + DeserializeOwned;
    type ConsensusState: ConsensusState + Serialize + DeserializeOwned;

    type Requester: tmlite::Requester<Self::Commit, Self::Header>;

    fn id(&self) -> &ChainId {
        &self.config().id
    }

    fn config(&self) -> &ChainConfig;
    fn rpc_client(&self) -> &RpcClient;
    fn requester(&self) -> &Self::Requester;
    fn trusting_period(&self) -> Duration;
    fn trust_threshold(&self) -> TrustThresholdFraction;
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
