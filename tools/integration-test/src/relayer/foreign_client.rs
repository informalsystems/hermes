use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::types::id::*;
use crate::types::tagged::*;

pub trait TaggedForeignClientExt<DstChain: ChainHandle, SrcChain: ChainHandle> {
    fn tagged_src_chain_id(&self) -> ChainId<SrcChain>;

    fn tagged_dst_chain_id(&self) -> ChainId<DstChain>;

    fn tagged_client_id(&self) -> ClientIdRef<DstChain, SrcChain>;
}

impl<DstChain: ChainHandle, SrcChain: ChainHandle> TaggedForeignClientExt<DstChain, SrcChain>
    for ForeignClient<DstChain, SrcChain>
{
    fn tagged_src_chain_id(&self) -> ChainId<SrcChain> {
        MonoTagged::new(self.src_chain().id())
    }

    fn tagged_dst_chain_id(&self) -> ChainId<DstChain> {
        MonoTagged::new(self.dst_chain().id())
    }

    fn tagged_client_id(&self) -> ClientIdRef<DstChain, SrcChain> {
        DualTagged::new(self.id())
    }
}
