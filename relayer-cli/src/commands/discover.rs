use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};


use crate::config::Config;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct DiscoverCmd {}

impl DiscoverCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        debug!("launching 'discover' command");
        discover_task(&config)
    }
}

impl Runnable for DiscoverCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

use petgraph::Graph;
use relayer::config::ChainConfig;
use relayer::channel::{ChannelConfig, ChannelConfigSide};
use ibc::ics24_host::identifier::{ConnectionId, ClientId, ChainId};
use petgraph::dot::{Dot, Config as DotConfig};

#[derive(Clone, Debug)]
pub struct Topo {
    pub chains: Vec<ChainId>,
    pub channels: Vec<ChannelConfig>, // TODO - assumes only one channel, change for many
    pub graph: Graph::<ChainConfig, ChannelConfig>
}

pub fn discover_task(config: &Config) -> Result<(), BoxError> {
    let n_chains = config.chains.len();
    let n_pairs = (n_chains * n_chains - 1)/2;
    let mut topo = Topo {
        chains: vec![ChainId::default(); n_chains],
        channels: vec![],
        graph: Graph::<ChainConfig, ChannelConfig>::new()
    };

    for mut chain in config.chains {
        let chain_idx = topo.graph.add_node(chain);
        topo.chains[chain_idx.index()] = chain.id.clone();
    }

    for chain_a in config.chains {
        for chain_b in config.chains {
            if chain_a.id >= chain_b.id {
                continue;
            }
            // TODO - query
            let a_config = ChannelConfigSide::new(
                chain_a.id.clone(),
                ClientId::default(),
                ConnectionId::default(),
                "transfer".parse().unwrap(),
                Default::default(),
            );
            let b_config = ChannelConfigSide::new(
                chain_a.id.clone(),
                ClientId::default(),
                ConnectionId::default(),
                "transfer".parse().unwrap(),
                Default::default(),
            );
            let channel = ChannelConfig {
                ordering: Default::default(),
                a_config,
                b_config,
            };

            let _channel_idx = topo.graph.add_edge(chain_a.id, chain_b.idx.unwrap(), channel);
        }
    }
    println!("{:?}", Dot::with_config(&topo.graph, &[DotConfig::EdgeNoLabel]));
    Ok(())
}
