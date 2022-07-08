use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::{Async, ErrorContext};
use crate::traits::packet::IbcPacket;
use crate::types::aliases::ClientId;

pub trait RelayContext: ErrorContext {
    type SrcChain: IbcChainContext<Self::DstChain, Error = Self::Error>;

    type DstChain: IbcChainContext<Self::SrcChain, Error = Self::Error>;

    type Packet: IbcPacket<Self::SrcChain, Self::DstChain> + Async;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;

    fn source_client_id(&self) -> &ClientId<Self::SrcChain, Self::DstChain>;

    fn destination_client_id(&self) -> &ClientId<Self::DstChain, Self::SrcChain>;
}
