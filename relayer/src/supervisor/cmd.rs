use crossbeam_channel::Sender;
use ibc::ics24_host::identifier::ChainId;

use crate::config::ChainConfig;

use super::dump_state::SupervisorState;

#[derive(Clone, Debug)]
pub enum ConfigUpdate {
    Add(ChainConfig),
    Remove(ChainId),
    Update(ChainConfig),
}

#[derive(Clone, Debug)]
pub enum SupervisorCmd {
    UpdateConfig(ConfigUpdate),
    DumpState(Sender<SupervisorState>),
}
