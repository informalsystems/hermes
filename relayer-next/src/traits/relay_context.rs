use super::chain_context::IbcChainContext;

pub trait RelayContext: Sized + Send + Sync + 'static {
    type Error;

    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error>;
    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error>;
}

pub trait RelayContextPair {
    type SrcContext: RelayContext;

    type DstContext: RelayContext<
        SrcChain = <Self::SrcContext as RelayContext>::DstChain,
        DstChain = <Self::SrcContext as RelayContext>::SrcChain,
        Error = <Self::SrcContext as RelayContext>::Error,
    >;

    fn source_context(&self) -> &Self::SrcContext;

    fn destination_context(&self) -> &Self::DstContext;
}
