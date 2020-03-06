use ::tendermint::rpc;

use relayer_modules::ics02_client::state::ConsensusState;

use crate::config::ChainConfig;

pub mod tendermint;

pub trait Chain {
    type Type;
    type ConsensusState: ConsensusState;

    fn config(&self) -> &ChainConfig;
    fn rpc_client(&self) -> &rpc::Client; // TODO: Define our own generic client interface?
}
