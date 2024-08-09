use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
pub use ibc_relayer_types::core::ics33_multihop::channel_path::{ConnectionHop, ConnectionHops};

use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    IncludeProof, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use crate::error::Error;
use crate::registry::get_global_registry;

pub fn build_hops_from_connection_ids(
    src_chain: &impl ChainHandle,
    connection_ids: &[ConnectionId],
) -> Result<ConnectionHops, Error> {
    let registry = get_global_registry();

    let mut connection_hops = Vec::new();

    let src_connection_id = connection_ids
        .first()
        .ok_or(Error::empty_connection_hop_ids())?
        .clone();

    let (src_hop_connection, _) = src_chain.query_connection(
        QueryConnectionRequest {
            connection_id: src_connection_id.clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    let (src_hop_conn_client_state, _) = src_chain.query_client_state(
        QueryClientStateRequest {
            client_id: src_hop_connection.client_id().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    connection_hops.push(ConnectionHop {
        connection: IdentifiedConnectionEnd::new(src_connection_id.clone(), src_hop_connection),
        src_chain_id: src_chain.id(),
        dst_chain_id: src_hop_conn_client_state.chain_id().clone(),
    });

    for hop_connection_id in connection_ids.iter().skip(1) {
        let hop_chain_id = connection_hops
            .last()
            .expect("connection hops is never empty")
            .dst_chain_id
            .clone();

        let hop_chain = match registry.get_or_spawn(&hop_chain_id) {
            Ok(chain) => chain,
            Err(_) => return Err(Error::spawn_error(hop_chain_id.clone())),
        };

        let (hop_connection, _) = hop_chain.query_connection(
            QueryConnectionRequest {
                connection_id: hop_connection_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        )?;

        let (hop_conn_client_state, _) = hop_chain.query_client_state(
            QueryClientStateRequest {
                client_id: hop_connection.client_id().clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        )?;

        connection_hops.push(ConnectionHop {
            connection: IdentifiedConnectionEnd::new(hop_connection_id.clone(), hop_connection),
            src_chain_id: hop_chain.id().clone(),
            dst_chain_id: hop_conn_client_state.chain_id().clone(),
        });
    }

    let connection_hops = ConnectionHops::new(connection_hops);

    Ok(connection_hops)
}
