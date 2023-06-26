/*!
   Constructs for the relay context.

   A relay context corresponds to the context that the relayer uses to relay
   IBC packets from a source chain to a destination chain in _one_ direction.
   It is made of two chain sub-contexts that act as the source and destination
   chain.

   At its core, a relay context should implement
   [`HasRelayChains`](traits::types::HasRelayChains), which declares the chain
   sub-contexts as well as the abstract types that are used when relaying.

   Since the relay context only supports relaying in one direction, two relay
   contexts are needed for the relayer to perform bi-directional relaying.
   To support relaying between different chain types, such as Cosmos to
   non-Cosmos chain relaying, the relay context implementation in the reverse
   direction may differ from the relay context in the original direction.

   A key feature the relay context provides is on performing relaying of
   a single packet, as defined by
   [`CanRelayPacket`](traits::packet_relayer::CanRelayPacket).
   The relay context also provides the important functionality of building
   the update client messages using
   [`CanBuildUpdateClientMessage`](traits::messages::update_client::CanBuildUpdateClientMessage)
   to update the client state of one chain to its counterparty chain.

   Compared to a single chain context, the relay context holds access to two
   chains, allowing it to perform operations that require access to both
   chains.
*/

pub mod impls;
pub mod traits;
pub mod types;
