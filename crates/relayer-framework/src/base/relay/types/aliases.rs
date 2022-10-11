use crate::base::relay::traits::context::RelayContext;

pub type Packet<Context> = <Context as RelayContext>::Packet;

pub type SrcChain<Context> = <Context as RelayContext>::SrcChain;

pub type DstChain<Context> = <Context as RelayContext>::DstChain;
