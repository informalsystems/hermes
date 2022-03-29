use crossbeam_channel::Sender;

use super::dump_state::SupervisorState;

#[derive(Clone, Debug)]
pub enum SupervisorCmd {
    DumpState(Sender<SupervisorState>),
}
