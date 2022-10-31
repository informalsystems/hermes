/*!
   Definition for extension trait methods for [`Connection`]
*/

use core::time::Duration;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConnectionRequest, QueryHeight};
use ibc_relayer::connection::{extract_connection_id, Connection, ConnectionSide};
use ibc_relayer_types::core::ics03_connection::connection::State as ConnectionState;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::timestamp::ZERO_DURATION;

use crate::error::Error;
use crate::types::id::{TaggedClientIdRef, TaggedConnectionId, TaggedConnectionIdRef};
use crate::types::tagged::DualTagged;
use crate::util::retry::assert_eventually_succeed;

/**
   An extension trait that provide helper methods to get tagged identifiers
   out of a [`Connection`].
*/
pub trait TaggedConnectionExt<ChainA: ChainHandle, ChainB: ChainHandle> {
    /**
       Get the connection ID from side A of the chain.
    */
    fn tagged_connection_id_a(&self) -> Option<TaggedConnectionIdRef<ChainA, ChainB>>;

    /**
       Get the connection ID from side B of the chain.
    */
    fn tagged_connection_id_b(&self) -> Option<TaggedConnectionIdRef<ChainB, ChainA>>;
}

pub trait TaggedConnectionEndExt<ChainA, ChainB> {
    fn tagged_counterparty_connection_id(&self) -> Option<TaggedConnectionId<ChainB, ChainA>>;
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> TaggedConnectionExt<ChainA, ChainB>
    for Connection<ChainA, ChainB>
{
    fn tagged_connection_id_a(&self) -> Option<TaggedConnectionIdRef<ChainA, ChainB>> {
        self.a_side.connection_id().map(DualTagged::new)
    }

    fn tagged_connection_id_b(&self) -> Option<TaggedConnectionIdRef<ChainB, ChainA>> {
        self.b_side.connection_id().map(DualTagged::new)
    }
}

impl<ChainA, ChainB> TaggedConnectionEndExt<ChainA, ChainB>
    for DualTagged<ChainA, ChainB, ConnectionEnd>
{
    fn tagged_counterparty_connection_id(&self) -> Option<TaggedConnectionId<ChainB, ChainA>> {
        self.contra_map(|c| c.counterparty().connection_id.clone())
            .transpose()
    }
}

pub fn init_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    client_id_a: &TaggedClientIdRef<ChainA, ChainB>,
    client_id_b: &TaggedClientIdRef<ChainB, ChainA>,
) -> Result<
    (
        TaggedConnectionId<ChainB, ChainA>,
        Connection<ChainB, ChainA>,
    ),
    Error,
> {
    let connection = Connection {
        delay_period: ZERO_DURATION,
        a_side: ConnectionSide::new(handle_a.clone(), (*client_id_a.value()).clone(), None),
        b_side: ConnectionSide::new(handle_b.clone(), (*client_id_b.value()).clone(), None),
    };

    let event = connection.build_conn_init_and_send()?;
    let connection_id = extract_connection_id(&event)?.clone();
    let connection2 = Connection::restore_from_event(handle_b.clone(), handle_a.clone(), &event)?;

    Ok((DualTagged::new(connection_id), connection2))
}

pub fn try_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    connection: &Connection<ChainA, ChainB>,
) -> Result<
    (
        TaggedConnectionId<ChainB, ChainA>,
        Connection<ChainB, ChainA>,
    ),
    Error,
> {
    let event = connection.build_conn_try_and_send()?;
    let connection_id = extract_connection_id(&event)?.clone();
    let connection2 = Connection::restore_from_event(handle_b.clone(), handle_a.clone(), &event)?;

    Ok((DualTagged::new(connection_id), connection2))
}

pub fn ack_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    connection: &Connection<ChainA, ChainB>,
) -> Result<
    (
        TaggedConnectionId<ChainB, ChainA>,
        Connection<ChainB, ChainA>,
    ),
    Error,
> {
    let event = connection.build_conn_ack_and_send()?;
    let connection_id = extract_connection_id(&event)?.clone();
    let connection2 = Connection::restore_from_event(handle_b.clone(), handle_a.clone(), &event)?;

    Ok((DualTagged::new(connection_id), connection2))
}

pub fn query_connection_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    connection_id: &TaggedConnectionIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, ConnectionEnd>, Error> {
    let (connection_end, _) = handle.query_connection(
        QueryConnectionRequest {
            connection_id: connection_id.into_value().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    Ok(DualTagged::new(connection_end))
}

pub fn query_identified_connection_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    connection_id: TaggedConnectionIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, IdentifiedConnectionEnd>, Error> {
    let (connection_end, _) = handle.query_connection(
        QueryConnectionRequest {
            connection_id: connection_id.into_value().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;
    Ok(DualTagged::new(IdentifiedConnectionEnd::new(
        connection_id.into_value().clone(),
        connection_end,
    )))
}

pub fn assert_eventually_connection_established<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    connection_id_a: &TaggedConnectionIdRef<ChainA, ChainB>,
) -> Result<TaggedConnectionId<ChainB, ChainA>, Error> {
    assert_eventually_succeed(
        "connection should eventually established",
        20,
        Duration::from_secs(1),
        || {
            let connection_end_a = query_connection_end(handle_a, connection_id_a)?;

            if !connection_end_a
                .value()
                .state_matches(&ConnectionState::Open)
            {
                return Err(Error::generic(eyre!(
                    "expected connection end A to be in open state"
                )));
            }

            let connection_id_b = connection_end_a
                .tagged_counterparty_connection_id()
                .ok_or_else(|| {
                    eyre!("expected counterparty connection id to present on open connection")
                })?;

            let connection_end_b = query_connection_end(handle_b, &connection_id_b.as_ref())?;

            if !connection_end_b
                .value()
                .state_matches(&ConnectionState::Open)
            {
                return Err(Error::generic(eyre!(
                    "expected connection end B to be in open state"
                )));
            }

            Ok(connection_id_b)
        },
    )
}
