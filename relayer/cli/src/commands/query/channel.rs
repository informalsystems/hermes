use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use relayer::query::channel::query_channel;

use relayer_modules::ics24_host::identifier::{ChannelId, PortId};

use crate::commands::utils::block_on;
use relayer::chain::tendermint::TendermintChain;
use relayer_modules::ics24_host::error::ValidationError;
use tendermint::chain::Id as ChainId;

#[derive(Command, Debug, Options)]
pub struct QueryChannelEndsCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the port to query")]
    port_id: Option<String>,

    #[options(free, help = "identifier of the channel to query")]
    channel_id: Option<String>,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryChannelOptions {
    port_id: PortId,
    channel_id: ChannelId,
    height: u64,
    proof: bool,
}

impl QueryChannelEndsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryChannelOptions), String> {
        let chain_id = self
            .chain_id
            .ok_or_else(|| "missing chain configuration".to_string())?;
        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == chain_id)
            .ok_or_else(|| "missing chain configuration".to_string())?;

        let port_id = self
            .port_id
            .as_ref()
            .ok_or_else(|| "missing port identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let channel_id = self
            .channel_id
            .as_ref()
            .ok_or_else(|| "missing channel identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryChannelOptions {
            port_id,
            channel_id,
            height: match self.height {
                Some(h) => h,
                None => 0 as u64,
            },
            proof: match self.proof {
                Some(proof) => proof,
                None => true,
            },
        };
        Ok((chain_config.clone(), opts))
    }
}

impl Runnable for QueryChannelEndsCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        // run with proof:
        // cargo run --bin relayer -- -c simple_config.toml query channel ends ibc0 transfer ibconexfer
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query channel ends ibc0 transfer ibconexfer -p false
        //
        // Note: currently both fail in amino_unmarshal_binary_length_prefixed().
        // To test this start a Gaia node and configure a channel using the go relayer.
        let chain = TendermintChain::from_config(chain_config).unwrap();
        let res = block_on(query_channel(
            &chain,
            opts.height,
            opts.port_id.clone(),
            opts.channel_id.clone(),
            opts.proof,
        ));
        match res {
            Ok(cs) => status_info!("channel query result: ", "{:?}", cs.channel),
            Err(e) => status_info!("channel query error: ", "{:?}", e),
        }
    }
}
