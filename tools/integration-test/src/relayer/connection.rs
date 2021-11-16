use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::Connection;

use crate::types::id::*;
use crate::types::tagged::*;

pub trait TaggedConnectionExt<ChainA: ChainHandle, ChainB: ChainHandle> {
    fn tagged_connection_id_a(&self) -> Option<ConnectionIdRef<ChainA, ChainB>>;

    fn tagged_connection_id_b(&self) -> Option<ConnectionIdRef<ChainB, ChainA>>;
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> TaggedConnectionExt<ChainA, ChainB>
    for Connection<ChainA, ChainB>
{
    fn tagged_connection_id_a(&self) -> Option<ConnectionIdRef<ChainA, ChainB>> {
        self.a_side.connection_id().map(DualTagged::new)
    }

    fn tagged_connection_id_b(&self) -> Option<ConnectionIdRef<ChainB, ChainA>> {
        self.b_side.connection_id().map(DualTagged::new)
    }
}
