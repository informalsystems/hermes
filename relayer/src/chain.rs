use std::time::Duration;

use anomaly::fail;
use serde::{de::DeserializeOwned, Serialize};

use ::tendermint::chain::Id as ChainId;
use ::tendermint::lite::types as tmlite;
use ::tendermint::lite::{self, Height, TrustThresholdFraction};
use ::tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics24_host::Path;
use ibc::try_from_raw::TryFromRaw;

use crate::config::ChainConfig;
use crate::error;
use std::error::Error;

mod cosmos;
pub use cosmos::CosmosSDKChain;
use prost_types::Any;

/// Handy type alias for the type of validator set associated with a chain
pub type ValidatorSet<Chain> = <<Chain as self::Chain>::Commit as tmlite::Commit>::ValidatorSet;

/// Defines a blockchain as understood by the relayer
pub trait Chain {
    /// Type of headers for this chain
    type Header: tmlite::Header + Send + Sync + Serialize + DeserializeOwned;

    /// Type of commits for this chain
    type Commit: tmlite::Commit + Send + Sync + Serialize + DeserializeOwned;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState + Send + Sync + Serialize + DeserializeOwned;

    /// Type of the client state for this chain
    type ClientState: ClientState;

    /// Type of RPC requester (wrapper around low-level RPC client) for this chain
    type Requester: tmlite::Requester<Self::Commit, Self::Header>;

    /// Error types defined by this chain
    type Error: Into<Box<dyn Error + Send + Sync + 'static>>;

    /// Perform a generic `query`, and return the corresponding deserialized response data.
    // This is going to be a blocking request.
    // From the "Asynchronous Programming in Rust" book:
    //   Important extensions like `async fn` syntax in trait methods are still unimplemented
    // https://rust-lang.github.io/async-book/01_getting_started/03_state_of_async_rust.html
    // DEPRECATED: implement abci_query instead. Since this will be removed before the next release
    // I'm commenting out the deprectaed warning. It would just confuse the clippy check in CI.
    //#[deprecated(since = "0.0.4", note = "please use `abci_query` instead")]
    fn query<T>(&self, data: Path, height: u64, prove: bool) -> Result<T, Self::Error>
    where
        T: TryFromRaw;

    /// Perform a generic `query` using ABCI, and return the corresponding response data.
    /// The naming is foreshadowing for an upcoming `grpc_query` function in the future.
    fn abci_query(&self, data: Path, height: u64, prove: bool) -> Result<Vec<u8>, Self::Error>;

    /// send a transaction with `msgs` to chain.
    fn send(&self, msgs: Vec<Any>) -> Result<(), Self::Error>;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        &self.config().id
    }

    /// Returns the chain's configuration
    fn config(&self) -> &ChainConfig;

    /// Get a low-level RPC client for this chain
    fn rpc_client(&self) -> &RpcClient;

    /// Get a higher-level RPC requester for this chain
    fn requester(&self) -> &Self::Requester;

    /// The trusting period configured for this chain
    fn trusting_period(&self) -> Duration;

    /// The unbonding period of this chain
    /// TODO - this is a GRPC query, needs to be implemented
    fn unbonding_period(&self) -> Duration;

    /// The trust threshold configured for this chain
    fn trust_threshold(&self) -> TrustThresholdFraction;
}

/// Query the latest height the chain is at via a RPC query
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

/// Query the latest header
pub async fn query_latest_header<C>(
    chain: &C,
) -> Result<lite::SignedHeader<C::Commit, C::Header>, error::Error>
where
    C: Chain,
{
    let h = query_latest_height(chain).await?;
    Ok(query_header_at_height::<C>(chain, h).await?)
}

/// Query a header at the given height via the RPC requester
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
