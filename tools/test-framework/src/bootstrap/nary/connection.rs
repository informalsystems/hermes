/*!
   Functions for bootstrapping N-ary number of connections.
*/

use core::time::Duration;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::bootstrap::binary::connection::{bootstrap_connection, BootstrapConnectionOptions};
use crate::error::Error;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::nary::foreign_client::ForeignClientPairs;
use crate::util::two_dim_hash_map::TwoDimMap;

/**
   Bootstrap a dynamic number of connections based on the
   given foreign clients.
   See [`crate::types::topology`] for more information.
*/
pub fn bootstrap_connections_dynamic<Handle: ChainHandle>(
    foreign_clients: &TwoDimMap<ForeignClient<Handle, Handle>>,
    connection_delay: Duration,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedConnections<Handle>, Error> {
    let mut connections: TwoDimMap<ConnectedConnection<Handle, Handle>> = TwoDimMap::new();

    for (src_chain, dst_chain, foreign_client) in foreign_clients.iter() {
        let connection = if let Some(counterparty_connection) =
            connections.get((dst_chain, src_chain))
        {
            counterparty_connection.clone().flip()
        } else {
            // No connection is found, will create one
            let client_a_to_b = foreign_client.clone();
            let client_b_to_a = foreign_clients.get((dst_chain, src_chain)).ok_or_else(|| {
                Error::generic(eyre!(
                    "No client entry found from chain `{}` to `{}`",
                    dst_chain,
                    src_chain,
                ))
            })?;
            let foreign_clients = ForeignClientPair::new(client_a_to_b, client_b_to_a.clone());

            let bootstrap_options = BootstrapConnectionOptions::default()
                .connection_delay(connection_delay)
                .bootstrap_with_random_ids(bootstrap_with_random_ids);

            bootstrap_connection(&foreign_clients, bootstrap_options)?
        };
        connections.insert((src_chain, dst_chain), connection);
    }

    Ok(DynamicConnectedConnections::new(connections))
}

pub fn bootstrap_connections<Handle: ChainHandle, const SIZE: usize>(
    foreign_clients: ForeignClientPairs<Handle, SIZE>,
    connection_delay: Duration,
    bootstrap_with_random_ids: bool,
) -> Result<ConnectedConnections<Handle, SIZE>, Error> {
    let connections = bootstrap_connections_dynamic(
        &foreign_clients.into_nested_vec(),
        connection_delay,
        bootstrap_with_random_ids,
    )?;

    connections.try_into()
}
