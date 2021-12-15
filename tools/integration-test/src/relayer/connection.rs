/*!
   Definition for extension trait methods for [`Connection`]
*/

use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::timestamp::ZERO_DURATION;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::{extract_connection_id, Connection, ConnectionSide};

use crate::error::Error;
use crate::types::id::{TaggedClientIdRef, TaggedConnectionId, TaggedConnectionIdRef};
use crate::types::tagged::DualTagged;

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
) -> Result<TaggedConnectionId<ChainB, ChainA>, Error> {
    let connection = Connection {
        delay_period: ZERO_DURATION,
        a_side: ConnectionSide::new(handle_a.clone(), (*client_id_a.value()).clone(), None),
        b_side: ConnectionSide::new(handle_b.clone(), (*client_id_b.value()).clone(), None),
    };

    let event = connection.build_conn_init_and_send()?;

    let connection_id = extract_connection_id(&event)?;

    Ok(DualTagged::new(connection_id.clone()))
}

pub fn query_connection_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    connection_id: &TaggedConnectionIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, ConnectionEnd>, Error> {
    let connection_end = handle.query_connection(connection_id.value(), Height::zero())?;

    Ok(DualTagged::new(connection_end))
}
