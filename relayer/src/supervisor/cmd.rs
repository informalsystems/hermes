use crossbeam_channel::Sender;
use ibc::core::ics24_host::identifier::ChainId;

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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CmdEffect {
    ConfigChanged,
    Nothing,
}

impl CmdEffect {
    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (CmdEffect::ConfigChanged, _) => CmdEffect::ConfigChanged,
            (_, CmdEffect::ConfigChanged) => CmdEffect::ConfigChanged,
            _ => self,
        }
    }
}
