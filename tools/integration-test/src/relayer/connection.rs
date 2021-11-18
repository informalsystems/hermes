/*!
   Definition for extension trait methods for [`Connection`]
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::connection::Connection;

use crate::types::id::TaggedConnectionIdRef;
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
