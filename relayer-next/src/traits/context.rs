pub trait RelayContext: Sized + Send + Sync + 'static {
    type Error;

    type SrcChain;
    type DstChain;
}

pub trait RelayContextPair {
    type SrcContext: RelayContext;

    type DstContext: RelayContext<
        SrcChain = <Self::SrcContext as RelayContext>::DstChain,
        DstChain = <Self::SrcContext as RelayContext>::SrcChain,
    >;
}
