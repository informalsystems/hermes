use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::util::task::TaskHandle;
use ibc_relayer::worker::client::spawn_refresh_client;

use crate::error::Error;
use crate::types::binary::foreign_client::ForeignClientPair;

pub fn spawn_refresh_client_tasks<ChainA: ChainHandle, ChainB: ChainHandle>(
    foreign_clients: &ForeignClientPair<ChainA, ChainB>,
) -> Result<[TaskHandle; 2], Error> {
    let refresh_task_a = spawn_refresh_client(foreign_clients.client_b_to_a.clone())
        .ok_or_else(|| eyre!("expect refresh task spawned"))?;

    let refresh_task_b = spawn_refresh_client(foreign_clients.client_a_to_b.clone())
        .ok_or_else(|| eyre!("expect refresh task spawned"))?;

    Ok([refresh_task_a, refresh_task_b])
}
