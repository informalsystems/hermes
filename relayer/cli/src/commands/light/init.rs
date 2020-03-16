use std::future::Future;
use std::time::{Duration, SystemTime};

// use crate::application::APPLICATION;
use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::lite::types::Header;
use tendermint::lite::Height;

use relayer::chain::tendermint::TendermintChain;
use relayer::chain::Chain;
use relayer::client::{trust_options::TrustOptions, Client};
use relayer::config::{ChainConfig, Config};
use relayer::store::mem::MemStore;
use relayer::store::Store;

#[derive(Command, Debug, Options)]
pub struct InitCmd {
    #[options(free, help = "identifier of the chain to initialize light client for")]
    chain_id: Option<ChainId>,

    #[options(help = "trusted header hash", short = "x")]
    hash: Option<Hash>,

    #[options(help = "trusted header height", short = "h")]
    height: Option<Height>,
}

#[derive(Clone, Debug)]
struct InitOptions {
    /// identifier of chain to initialize light client for
    chain_id: ChainId,

    /// trusted header hash
    trusted_hash: Hash,

    /// trusted header height
    trusted_height: Height,
}

impl InitCmd {
    fn validate_options(&self) -> Result<InitOptions, &'static str> {
        match (&self.chain_id, &self.hash, self.height) {
            (Some(chain_id), Some(trusted_hash), Some(trusted_height)) => Ok(InitOptions {
                chain_id: *chain_id,
                trusted_hash: *trusted_hash,
                trusted_height,
            }),
            (None, _, _) => Err("missing chain identifier"),
            (_, None, _) => Err("missing trusted hash"),
            (_, _, None) => Err("missing trusted height"),
        }
    }
}

impl Runnable for InitCmd {
    /// Initialize the light client for the given chain
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options() {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(opts) => opts,
        };

        // FIXME: This just hangs and never runs the given future
        // abscissa_tokio::run(&APPLICATION, run_init(&*config, opts)).unwrap();

        block_on(run_init(config.clone(), opts));
    }
}

async fn run_init(config: Config, opts: InitOptions) {
    status_info!("Options", "{:?}", opts);

    for chain_config in config.chains {
        let opts = opts.clone();

        status_info!(
            "Relayer",
            "Spawning light client for chain {}",
            chain_config.id
        );

        let _handle = tokio::spawn(async move {
            let client = create_client(chain_config, opts).await;
            update_headers(client).await;
        });
    }

    start_relayer().await
}

async fn start_relayer() {
    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        interval.tick().await;
        status_info!("Relayer", "Relayer is running")
    }
}

async fn update_headers<C: Chain, S: Store<C>>(mut client: Client<C, S>) {
    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        let result = client.update(SystemTime::now()).await;
        match result {
            Ok(Some(trusted_state)) => status_ok!(
                client.chain().id(),
                "Updated to trusted state: {} at {}",
                trusted_state.header().hash(),
                trusted_state.header().height()
            ),

            Ok(None) => status_info!(client.chain().id(), "Ignoring update to a previous state"),
            Err(err) => status_info!(client.chain().id(), "Error when updating headers: {}", err),
        }

        interval.tick().await;
    }
}

async fn create_client(
    chain_config: ChainConfig,
    opts: InitOptions,
) -> Client<TendermintChain, MemStore<TendermintChain>> {
    let store = MemStore::new();

    let trust_options = TrustOptions::new(
        opts.trusted_hash,
        opts.trusted_height,
        chain_config.trusting_period,
        Default::default(),
    )
    .unwrap();

    let chain = TendermintChain::from_config(chain_config).unwrap();

    Client::new(chain, store, trust_options).await.unwrap()
}

fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
