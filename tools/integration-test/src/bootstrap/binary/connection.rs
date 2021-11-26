/*!
    Helper functions for bootstrapping a connection between two chains.
*/

use eyre::{eyre, Report as Error};
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::default;
use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer::foreign_client::ForeignClient;
use tracing::{debug, info};

use crate::relayer::connection::TaggedConnectionExt;
use crate::relayer::foreign_client::TaggedForeignClientExt;
use crate::types::binary::client::ConnectedClients;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::id::TaggedClientIdRef;
use crate::util::random::random_u64_range;

/**
   Create a new [`ConnectedConnection`] using the foreign clients with
   initialized client IDs.
*/
pub fn bootstrap_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
) -> Result<ConnectedConnection<ChainA, ChainB>, Error> {
    let chain_a = client_a_to_b.src_chain();
    let chain_b = client_a_to_b.dst_chain();

    let client_id_a = client_b_to_a.tagged_client_id();
    let client_id_b = client_a_to_b.tagged_client_id();

    pad_connection_id(&chain_a, &chain_b, &client_id_a, &client_id_b)?;

    pad_connection_id(&chain_b, &chain_a, &client_id_b, &client_id_a)?;

    let connection = Connection::new(
        client_b_to_a.clone(),
        client_a_to_b.clone(),
        default::connection_delay(),
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

    let connected_connection = ConnectedConnection {
        connection,

        client: ConnectedClients {
            client_id_a: client_id_a.cloned(),

            client_id_b: client_id_b.cloned(),
        },

        connection_id_a,

        connection_id_b,
    };

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
) -> Result<(), Error> {
    for i in 0..random_u64_range(1, 6) {
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
