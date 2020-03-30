use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use core::future::Future;
use relayer_modules::ics24_host::client::ClientId;
use tendermint::net;
use tokio::runtime::Builder;

#[derive(Command, Debug, Options)]
pub struct QueryClientsCmd {
    #[options(free, help = "rpc address")]
    // TODO replace this with the chain-id string and retrieve the rpc_addr from `Chain`
    rpc_addr: Option<net::Address>,
    height: Option<u64>,
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryOptions<'a> {
    /// identifier of chain for which to query the light client
    rpc_addr: &'a net::Address,
    height: u64,
    proof: bool,
}

impl QueryClientsCmd {
    fn validate_options(&self) -> Result<QueryOptions<'_>, String> {
        match (&self.rpc_addr, self.height, self.proof) {
            (Some(rpc_addr), Some(height), Some(proof)) => Ok(QueryOptions {
                rpc_addr,
                height,
                proof,
            }),

            (None, _, _) => Err(format!("missing rpc address")),
            (Some(rpc_addr), None, Some(proof)) => Ok(QueryOptions {
                rpc_addr,
                height: 0 as u64,
                proof,
            }),
            (Some(rpc_addr), Some(height), None) => Ok(QueryOptions {
                rpc_addr,
                height,
                proof: false,
            }),
            (Some(rpc_addr), None, None) => Ok(QueryOptions {
                rpc_addr,
                height: 0 as u64,
                proof: false,
            }),
        }
    }
}

use relayer::query::client_consensus_state::query_client_consensus_state;
use relayer::query::client_state::query_client_latest_state;

use relayer::chain::tendermint::TendermintChain;
use relayer::config::ChainConfig;
use std::str::FromStr;
use std::time::Duration;
use tendermint::chain::Id as ChainId;

impl Runnable for QueryClientsCmd {
    fn run(&self) {
        let opts = match self.validate_options() {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(opts) => opts,
        };
        status_info!("Options", "{:?}", opts);

        // TODO remove soon and replace with proper sequence
        // run without proof
        // export RUST_BACKTRACE=1 ; cargo run query clients localhost:26657 -p false
        // this causes earlier error in ibc_query() -> `.map_err(|e| error::Kind::Rpc.context(e))?;:`
        //
        // run with proof:
        // export RUST_BACKTRACE=1 ; cargo run query clients localhost:26657
        // this one fails in amino_unmarshal_binary_length_prefixed() as expected
        //
        // To test this start a Gaia node and configure a client with the go relayer.
        // Proper way is to query client state (not yet implemented), get the consensus_height from
        // the response and then query the consensus state. In the absence of this, look at logs
        // and check the height :(
        let consensus_height = opts.height;

        // Also, the relayer should have been started with config, chain information parsed and
        // the `Chain` already created. This also is not implemented therefore the weird sequence
        // below.
        let client_id = ClientId::from_str("ibconeclient").unwrap();
        let chain_id = ChainId::from_str("ibc0").unwrap();
        let chain_height = 0 as u64;

        let chain = TendermintChain::from_config(ChainConfig {
            id: chain_id,
            rpc_addr: opts.rpc_addr.clone(),
            account_prefix: "".to_string(),
            key_name: "".to_string(),
            client_ids: vec![],
            gas: 0,
            trusting_period: Duration::from_secs(336 * 60 * 60),
        })
        .unwrap();

        if true {
            let _res = block_on(query_client_consensus_state(
                &chain,
                chain_height,
                client_id.clone(),
                consensus_height,
                opts.proof,
            ))
            .unwrap();
        }

        let _res = block_on(query_client_latest_state(
            &chain,
            chain_height,
            client_id.clone(),
            opts.proof,
        ))
        .unwrap();
        // end remove soon
    }
}

fn block_on<F: Future>(future: F) -> F::Output {
    Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
