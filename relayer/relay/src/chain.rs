use ::tendermint::lite::types as tmlite;
use ::tendermint::rpc::Client as RpcClient;

use relayer_modules::ics02_client::state::ConsensusState;

use crate::config::ChainConfig;

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
