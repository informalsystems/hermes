/*!
   Definition for extension trait methods for [`Connection`]
*/

use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::{Connection, ConnectionSide};

use crate::error::Error;
use crate::types::id::{TaggedClientIdRef, TaggedConnectionIdRef};
use crate::types::tagged::*;

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

pub fn init_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    client_id_a: &TaggedClientIdRef<ChainA, ChainB>,
    client_id_b: &TaggedClientIdRef<ChainB, ChainA>,
) -> Result<Connection<ChainA, ChainB>, Error> {
    let connection = Connection {
        delay_period: ZERO_DURATION,
        a_side: ConnectionSide::new(handle_a.clone(), (*client_id_a.value()).clone(), None),
        b_side: ConnectionSide::new(handle_b.clone(), (*client_id_b.value()).clone(), None),
    };

    connection.build_conn_init_and_send()?;

    Ok(connection)
}
