/*!
   Definition for extension trait methods for [`ForeignClient`]
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::types::id::{TaggedChainId, TaggedClientIdRef};
use crate::types::tagged::*;

/**
   An extension trait for providing methods for getting tagged identifiers
   out of a [`ForeignClient`].
*/
pub trait TaggedForeignClientExt<DstChain: ChainHandle, SrcChain: ChainHandle> {
    /**
       Get the source chain ID.
    */
    fn tagged_src_chain_id(&self) -> TaggedChainId<SrcChain>;

    /**
       Get the destination chain ID.
    */
    fn tagged_dst_chain_id(&self) -> TaggedChainId<DstChain>;

    /**
       Get the client ID of the destination chain that corresponds
       to the source chain.
    */
    fn tagged_client_id(&self) -> TaggedClientIdRef<DstChain, SrcChain>;
}

impl<DstChain: ChainHandle, SrcChain: ChainHandle> TaggedForeignClientExt<DstChain, SrcChain>
    for ForeignClient<DstChain, SrcChain>
{
    fn tagged_src_chain_id(&self) -> TaggedChainId<SrcChain> {
        MonoTagged::new(self.src_chain().id())
    }

    fn tagged_dst_chain_id(&self) -> TaggedChainId<DstChain> {
        MonoTagged::new(self.dst_chain().id())
    }

    fn tagged_client_id(&self) -> TaggedClientIdRef<DstChain, SrcChain> {
        DualTagged::new(self.id())
    }
}
