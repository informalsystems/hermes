/*!
    Helper functions for bootstrapping a connection between two chains.
*/

use core::time::Duration;
use eyre::{eyre, Report as Error};
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::default::connection_delay as default_connection_delay;
use ibc_relayer::connection::{Connection, ConnectionSide};
use tracing::{debug, info};

use crate::relayer::connection::TaggedConnectionExt;
use crate::types::binary::client::ClientIdPair;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::id::TaggedClientIdRef;
use crate::util::random::random_u64_range;

pub struct BootstrapConnectionOptions {
    pub connection_delay: Duration,
    pub pad_connection_id_a: u64,
    pub pad_connection_id_b: u64,
}

/**
   Create a new [`ConnectedConnection`] using the foreign clients with
   initialized client IDs.
*/
pub fn bootstrap_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    foreign_clients: &ForeignClientPair<ChainA, ChainB>,
    options: BootstrapConnectionOptions,
) -> Result<ConnectedConnection<ChainA, ChainB>, Error> {
    let chain_a = foreign_clients.handle_a();
    let chain_b = foreign_clients.handle_b();

    let client_id_a = foreign_clients.client_id_a();
    let client_id_b = foreign_clients.client_id_b();

    pad_connection_id(
        &chain_a,
        &chain_b,
        &client_id_a,
        &client_id_b,
        options.pad_connection_id_a,
    )?;
    pad_connection_id(
        &chain_b,
        &chain_a,
        &client_id_b,
        &client_id_a,
        options.pad_connection_id_b,
    )?;

    let connection = Connection::new(
        foreign_clients.client_b_to_a.clone(),
        foreign_clients.client_a_to_b.clone(),
        options.connection_delay,
    )?;

    let connection_id_a = connection
        .tagged_connection_id_a()
        .ok_or_else(|| eyre!("expected connection id to present"))?
        .cloned();

    let connection_id_b = connection
        .tagged_connection_id_b()
        .ok_or_else(|| eyre!("expected connection id to present"))?
        .cloned();

    info!(
        "created new chain/client/connection from {}/{}/{} to {}/{}/{}",
        chain_a.id(),
        client_id_a,
        connection_id_a,
        chain_b.id(),
        client_id_b,
        connection_id_b,
    );

    let connected_connection = ConnectedConnection::new(
        ClientIdPair::new(client_id_a.cloned(), client_id_b.cloned()),
        connection,
        connection_id_a,
        connection_id_b,
    );

    Ok(connected_connection)
}

/**
   Create a random number of dummy connection IDs so that the bootstrapped
   connection ID is random instead of being always `connection-0`.

   This would help us catch bugs where the connection IDs are used at
   the wrong side of the chain, but still got accepted because the
   connection IDs on both sides are the same.
*/
pub fn pad_connection_id<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    client_id_a: &TaggedClientIdRef<ChainA, ChainB>,
    client_id_b: &TaggedClientIdRef<ChainB, ChainA>,
    pad_count: u64,
) -> Result<(), Error> {
    for i in 0..pad_count {
        debug!(
            "creating new connection id {} on chain {}",
            i + 1,
            chain_a.id()
        );

        let connection: Connection<ChainB, ChainA> = Connection {
            delay_period: ZERO_DURATION,
            a_side: ConnectionSide::new(chain_b.clone(), client_id_b.cloned().into_value(), None),
            b_side: ConnectionSide::new(chain_a.clone(), client_id_a.cloned().into_value(), None),
        };

        connection.build_conn_init_and_send()?;
    }

    Ok(())
}

impl Default for BootstrapConnectionOptions {
    fn default() -> Self {
        Self {
            connection_delay: default_connection_delay(),
            pad_connection_id_a: 0,
            pad_connection_id_b: 0,
        }
    }
}

impl BootstrapConnectionOptions {
    pub fn connection_delay(mut self, connection_delay: Duration) -> Self {
        self.connection_delay = connection_delay;
        self
    }

    pub fn bootstrap_with_random_ids(mut self, bootstrap_with_random_ids: bool) -> Self {
        if bootstrap_with_random_ids {
            self.pad_connection_id_a = random_u64_range(0, 6);
            self.pad_connection_id_b = random_u64_range(0, 6);
        } else {
            self.pad_connection_id_a = 0;
            self.pad_connection_id_b = 1;
        }

        self
    }
}
