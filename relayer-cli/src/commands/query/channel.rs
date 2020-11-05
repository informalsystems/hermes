use crate::prelude::*;
use std::convert::TryInto;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};

use ibc::ics04_channel::channel::ChannelEnd;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::ics24_host::Path::ChannelEnds;

use crate::error::{Error, Kind};
use ibc::ics24_host::error::ValidationError;
use relayer::chain::{Chain, CosmosSDKChain};
use tendermint::chain::Id as ChainId;
use tendermint_proto::DomainType;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryChannelEndCmd {
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

impl QueryChannelEndCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryChannelOptions), String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "missing chain identifier".to_string())?;
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
            height: self.height.unwrap_or(0_u64),
            proof: self.proof.unwrap_or(true),
        };
        Ok((chain_config.clone(), opts))
    }
}

impl Runnable for QueryChannelEndCmd {
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

        // run without proof:
        // cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query channel end ibc-test firstport firstchannel --height 3 -p false
        let chain = CosmosSDKChain::from_config(chain_config).unwrap();
        let res: Result<ChannelEnd, Error> = chain
            .query(
                ChannelEnds(opts.port_id, opts.channel_id),
                opts.height.try_into().unwrap(),
                opts.proof,
            )
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| ChannelEnd::decode_vec(&v).map_err(|e| Kind::Query.context(e).into()));

        match res {
            Ok(cs) => status_info!("Result for channel end query: ", "{:?}", cs),
            Err(e) => status_info!("Error encountered on channel end query:", "{}", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::commands::query::channel::QueryChannelEndCmd;
    use relayer::config::parse;

    #[test]
    fn parse_channel_query_end_parameters() {
        let default_params = QueryChannelEndCmd {
            chain_id: Some("ibc0".to_string().parse().unwrap()),
            port_id: Some("transfer".to_string().parse().unwrap()),
            channel_id: Some("testchannel".to_string().parse().unwrap()),
            height: None,
            proof: None,
        };

        struct Test {
            name: String,
            params: QueryChannelEndCmd,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "No chain specified".to_string(),
                params: QueryChannelEndCmd {
                    chain_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryChannelEndCmd {
                    chain_id: Some("notibc0oribc1".to_string().parse().unwrap()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No port id specified".to_string(),
                params: QueryChannelEndCmd {
                    port_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct port (alphanumeric)".to_string(),
                params: QueryChannelEndCmd {
                    port_id: Some("p34".to_string()),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Incorrect port identifier (contains invalid character)".to_string(),
                params: QueryChannelEndCmd {
                    port_id: Some("p34^".to_string()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No channel id specified".to_string(),
                params: QueryChannelEndCmd {
                    channel_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: QueryChannelEndCmd {
                    channel_id: Some("chshort".to_string()),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/two_chains.toml"
        );

        let config = parse(path).unwrap();

        for test in tests {
            let res = test.params.validate_options(&config);

            match res {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "validate_options should have failed for test {}",
                        test.name
                    );
                }
                Err(err) => {
                    assert!(
                        !test.want_pass,
                        "validate_options failed for test {}, \nerr {}",
                        test.name, err
                    );
                }
            }
        }
    }
}
