

pub trait MockRelay: Async {

    type SrcChain: MockChain;

    type DstChain: MockChain;

    fn src_chain(&self) -> &Arc<Self::SrcChain>;

    fn dst_chain(&self) -> &Arc<Self::DstChain>;
}