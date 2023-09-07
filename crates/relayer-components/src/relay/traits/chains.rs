use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::chain::types::aliases::ClientId;
use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;

/**
    This covers the minimal abstract types that are used inside a relay context.

    A relay context is made of two chain sub-contexts,
    [`SrcChain`](Self::SrcChain) and [`DstChain`](Self::DstChain), that are
    connected to each others. This is reflected by both types being required
    to implement [`HasIbcPacketTypes`] with each others being the counterparty.

    The relay context also has an abstract [`Packet`](crate::relay::traits::packet::HasRelayPacket::Packet) type, which
    represents the IBC packet sent from the source chain to the destination
    chain. In other words, the relay context only covers relaying of IBC packets
    in one direction. To support bi-directional relaying between two chains,
    the relayer will use two relay contexts with the source and destination
    chains flipped in the second relay context.

    A relay context also implicitly assumes that the two chains are connected
    by a pair of IBC clients. This is required so that the relay context
    can build the UpdateClient messages without requiring to explicitly
    specify the client IDs. If two chains are connected through more than one
    IBC client pairs, they should be handled by separate relay contexts.

    On the other hand, it is possible to relay packets from multiple channels
    and connections, given that they are from the same IBC clients. This is
    ok because IBC does not differentiate messages from different channels
    and connections. Note however that concrete relay contexts may impose
    additional constraints such as restricting a relay context to handle
    only a single channel or connection.
*/
pub trait HasRelayChains: HasErrorType {
    type Packet: Async;

    /**
        A source chain context that has the IBC chain types that are correspond
        to the destination chain.
    */
    type SrcChain: HasErrorType
        + HasIbcChainTypes<Self::DstChain>
        + HasIbcPacketTypes<Self::DstChain, OutgoingPacket = Self::Packet>;

    /**
        A destination chain context that has the IBC chain types that are correspond
        to the source chain.
    */
    type DstChain: HasErrorType
        + HasIbcChainTypes<Self::SrcChain>
        + HasIbcPacketTypes<Self::SrcChain, IncomingPacket = Self::Packet>;

    /**
        Get a reference to the source chain context from the relay context.
    */
    fn src_chain(&self) -> &Self::SrcChain;

    /**
        Get a reference to the destination chain context from the relay context.
    */
    fn dst_chain(&self) -> &Self::DstChain;

    fn src_chain_error(e: <Self::SrcChain as HasErrorType>::Error) -> Self::Error;

    fn dst_chain_error(e: <Self::DstChain as HasErrorType>::Error) -> Self::Error;

    /**
        Get the client ID on the source chain that corresponds to the destination
        chain.

        This shows that the relay context is required to have an implicit IBC
        client. On the other hand, there are no accessor methods for getting
        the connection and channel IDs, because a relay context may handle
        more than one of them.
    */
    fn src_client_id(&self) -> &ClientId<Self::SrcChain, Self::DstChain>;

    /**
        Get the client ID on the destination chain that corresponds to the source
        chain.
    */
    fn dst_client_id(&self) -> &ClientId<Self::DstChain, Self::SrcChain>;
}
