/*!
   Functions for bootstrapping N-ary number of connections.
*/

use core::time::Duration;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;
use std::collections::HashMap;

use crate::bootstrap::binary::connection::{bootstrap_connection, BootstrapConnectionOptions};
use crate::error::Error;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::nary::foreign_client::ForeignClientPairs;
use crate::util::two_dim_hash_map::TwoDimHashMap;

/**
   Bootstrap a dynamic number of connections based on the
   given foreign clients.
   See [`crate::types::topology`] for more information.
*/
pub fn bootstrap_connections_dynamic<Handle: ChainHandle>(
    foreign_clients: &TwoDimHashMap<ForeignClient<Handle, Handle>>,
    connection_delay: Duration,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedConnections<Handle>, Error> {
    let mut connections: HashMap<usize, HashMap<usize, ConnectedConnection<Handle, Handle>>> =
        HashMap::new();

    for foreign_client in foreign_clients.map.iter() {
        let mut inner_connections: HashMap<usize, ConnectedConnection<Handle, Handle>> =
            HashMap::new();

        for client in foreign_client.1.iter() {
            let connection = if let Some(counterparty_connections) = connections.get(client.0) {
                let counterparty_connection = counterparty_connections
                    .get(foreign_client.0)
                    .ok_or_else(|| {
                        Error::generic(eyre!(
                            "No connection entry found from chain `{}` to `{}`",
                            client.0,
                            foreign_client.0
                        ))
                    })?;
                counterparty_connection.clone().flip()
            } else {
                // No connection is found, will create one
                let client_a_to_b = client.1.clone();
                let client_b_to_a = foreign_clients
                    .get((*client.0, *foreign_client.0))
                    .ok_or_else(|| {
                        Error::generic(eyre!(
                            "No client entry found from chain `{}` to `{}`",
                            client.0,
                            foreign_client.0
                        ))
                    })?;
                let foreign_clients = ForeignClientPair::new(client_a_to_b, client_b_to_a.clone());

                let bootstrap_options = BootstrapConnectionOptions::default()
                    .connection_delay(connection_delay)
                    .bootstrap_with_random_ids(bootstrap_with_random_ids);

                bootstrap_connection(&foreign_clients, bootstrap_options)?
            };

            inner_connections.insert(*client.0, connection);
        }
        connections.insert(*foreign_client.0, inner_connections);
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
