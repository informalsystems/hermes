use crate::relay::traits::types::{HasRelayChains, HasRelayPacket};

pub type Packet<Context> = <Context as HasRelayPacket>::Packet;

pub type SrcChain<Context> = <Context as HasRelayChains>::SrcChain;

pub type DstChain<Context> = <Context as HasRelayChains>::DstChain;
