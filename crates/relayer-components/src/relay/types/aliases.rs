use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::packet::HasRelayPacket;

pub type Packet<Context> = <Context as HasRelayPacket>::Packet;

pub type SrcChain<Context> = <Context as HasRelayChains>::SrcChain;

pub type DstChain<Context> = <Context as HasRelayChains>::DstChain;
