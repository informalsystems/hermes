use crate::base::all_for_one::runtime::AfoBaseRuntime;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::runtime::traits::channel::{CanCreateChannels, CanStreamReceiver, CanUseChannels};
use crate::full::runtime::traits::spawn::HasSpawner;

pub trait AfoFullRuntime:
    AfoBaseRuntime + HasSpawner + CanCreateChannels + CanStreamReceiver + CanUseChannels
{
}

impl<Runtime> AfoFullRuntime for Runtime where
    Runtime: AfoBaseRuntime + HasSpawner + CanCreateChannels + CanStreamReceiver + CanUseChannels
{
}

pub trait HasAfoFullRuntime: HasRuntime<Runtime = Self::AfoFullRuntime> {
    type AfoFullRuntime: AfoFullRuntime;
}

impl<Context, Runtime> HasAfoFullRuntime for Context
where
    Context: HasRuntime<Runtime = Runtime>,
    Runtime: AfoFullRuntime,
{
    type AfoFullRuntime = Runtime;
}
