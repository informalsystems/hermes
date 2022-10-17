use crate::base::relay::traits::types::HasRelayTypes;

pub type Packet<Context> = <Context as HasRelayTypes>::Packet;

pub type SrcChain<Context> = <Context as HasRelayTypes>::SrcChain;

pub type DstChain<Context> = <Context as HasRelayTypes>::DstChain;
