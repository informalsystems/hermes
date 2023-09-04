use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::relay::traits::chains::HasRelayChains;

pub type Packet<Relay> = <Relay as HasRelayChains>::Packet;

pub type SrcChain<Relay> = <Relay as HasRelayChains>::SrcChain;

pub type DstChain<Relay> = <Relay as HasRelayChains>::DstChain;

pub type SrcConnectionId<Relay> =
    <SrcChain<Relay> as HasIbcChainTypes<DstChain<Relay>>>::ConnectionId;

pub type DstConnectionId<Relay> =
    <DstChain<Relay> as HasIbcChainTypes<SrcChain<Relay>>>::ConnectionId;

pub type SrcPortId<Relay> = <SrcChain<Relay> as HasIbcChainTypes<DstChain<Relay>>>::PortId;

pub type DstPortId<Relay> = <DstChain<Relay> as HasIbcChainTypes<SrcChain<Relay>>>::PortId;

pub type SrcChannelId<Relay> = <SrcChain<Relay> as HasIbcChainTypes<DstChain<Relay>>>::ChannelId;

pub type DstChannelId<Relay> = <DstChain<Relay> as HasIbcChainTypes<SrcChain<Relay>>>::ChannelId;
