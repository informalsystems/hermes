use std::future::Future;

// use crate::application::APPLICATION;
use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use relayer::config::Config;

use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::lite::Height;

#[derive(Command, Debug, Options)]
pub struct InitCmd {
    #[options(free, help = "identifier of the chain to initialize light client for")]
    chain_id: Option<ChainId>,

    #[options(help = "trusted header hash", short = "x")]
    hash: Option<Hash>,

    #[options(help = "trusted header height", short = "h")]
    height: Option<Height>,
}

#[derive(Debug)]
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

        block_on(run_init(&*config, opts));
    }
}

pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}

async fn run_init(config: &Config, opts: InitOptions) {
    use relayer::chain::tendermint::TendermintChain;
    use relayer::client::{trust_options::TrustOptions, Client};
    use relayer::store::mem::MemStore;

    status_info!("Options", "{:?}", opts);

    let chain_config = config.chains[0].clone();

    let store = MemStore::<TendermintChain>::new();
    let trust_options = TrustOptions::new(
        opts.trusted_hash,
        opts.trusted_height,
        chain_config.trusting_period,
        Default::default(),
    )
    .unwrap();

    let chain = TendermintChain::from_config(chain_config).unwrap();
    let client = Client::new(chain, store, trust_options).await.unwrap();

    status_ok!(
        "Success",
        "Last trusted state:\n{:#?}",
        client.last_trusted_state()
    );
}
