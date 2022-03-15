/*!
   Functions for bootstrapping N-ary number of connections.
*/

use core::convert::TryInto;
use core::time::Duration;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::bootstrap::binary::connection::bootstrap_connection;
use crate::error::Error;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::nary::foreign_client::ForeignClientPairs;
use crate::util::array::assert_same_dimension;

/**
   Bootstrap a dynamic number of connections based on the
   given foreign client NxN matrix.
*/
pub fn bootstrap_connections_dynamic<Handle: ChainHandle>(
    foreign_clients: &Vec<Vec<ForeignClient<Handle, Handle>>>,
    connection_delay: Duration,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedConnections<Handle>, Error> {
    let size = foreign_clients.len();

    assert_same_dimension(size, foreign_clients)?;

    let mut connections: Vec<Vec<ConnectedConnection<Handle, Handle>>> = Vec::new();

    for (i, foreign_clients_b) in foreign_clients.iter().enumerate() {
        let mut connections_b: Vec<ConnectedConnection<Handle, Handle>> = Vec::new();

        for (j, foreign_client) in foreign_clients_b.iter().enumerate() {
            if i <= j {
                let counter_foreign_client = &foreign_clients[j][i];
                let foreign_clients =
                    ForeignClientPair::new(foreign_client.clone(), counter_foreign_client.clone());

                let connection = bootstrap_connection(
                    &foreign_clients,
                    connection_delay,
                    bootstrap_with_random_ids,
                )?;

                connections_b.push(connection);
            } else {
                let counter_connection = &connections[j][i];
                let connection = counter_connection.clone().flip();

                connections_b.push(connection);
            }
        }

        connections.push(connections_b);
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
