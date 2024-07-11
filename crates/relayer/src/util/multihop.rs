use std::convert::TryFrom;

use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
pub use ibc_relayer_types::core::ics33_multihop::channel_path::{ConnectionHop, ConnectionHops};

use crate::chain::handle::ChainHandle;
use crate::chain::requests::{
    IncludeProof, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use crate::error::Error;
use crate::registry::get_global_registry;

pub struct RawConnectionHops<'a, Chain: ChainHandle> {
    pub src_chain: &'a Chain,
    pub conn_hop_ids: Vec<ConnectionId>,
}

impl<'a, Chain: ChainHandle> TryFrom<RawConnectionHops<'a, Chain>> for ConnectionHops {
    type Error = Error;

    fn try_from(raw_conn_hops: RawConnectionHops<'a, Chain>) -> Result<Self, Error> {
        let registry = get_global_registry();
        let mut connection_hops = Vec::new();

        let src_connection_id = raw_conn_hops
            .conn_hop_ids
            .first()
            .expect("handle this properly") // ADD PROPER ERROR HANDLING HERE
            .clone();

        let (src_hop_connection, _) = raw_conn_hops.src_chain.query_connection(
            QueryConnectionRequest {
                connection_id: src_connection_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        )?;

        let (src_hop_conn_client_state, _) = raw_conn_hops.src_chain.query_client_state(
            QueryClientStateRequest {
                client_id: src_hop_connection.client_id().clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        )?;

        connection_hops.push(ConnectionHop {
            connection: IdentifiedConnectionEnd::new(src_connection_id.clone(), src_hop_connection),
            src_chain_id: raw_conn_hops.src_chain.id().clone(),
            dst_chain_id: src_hop_conn_client_state.chain_id().clone(),
        });

        //~ Assemble the remaining hops after the source chain's hop
        for connection_id in raw_conn_hops.conn_hop_ids.iter().skip(1) {
            //~ Get the ID of the chain that the previous hop points to
            let hop_chain_id = connection_hops
                .last()
                .expect("connection hops is never empty")
                .dst_chain_id
                .clone();

            //~ With the ID of the chain the prev hop point to, spawn the chain to make the queries
            let hop_chain = match registry.get_or_spawn(&hop_chain_id) {
                Ok(chain) => chain,
                Err(_) => return Err(Error::spawn_error(hop_chain_id.clone())),
            };

            let (hop_connection, _) = hop_chain.query_connection(
                QueryConnectionRequest {
                    connection_id: connection_id.clone(),
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
                connection: IdentifiedConnectionEnd::new(connection_id.clone(), hop_connection),
                src_chain_id: hop_chain.id().clone(),
                dst_chain_id: hop_conn_client_state.chain_id().clone(),
            });
        }

        let connection_hops = ConnectionHops::new(connection_hops);
        dbg!(&connection_hops);
        Ok(connection_hops)
    }
}
