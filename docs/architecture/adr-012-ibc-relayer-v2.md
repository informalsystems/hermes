# ADR 012: New Relayer Architecture

# Changelog

* 2022-11-10: Initial Draft

# Context and Problem Statement

The current Hermes relayer, hereby called v1 relayer in this document, was
implemented at a time when the Cosmos ecosystem was still very new, and the
idea of cross-chain communication with IBC was still a novel concept. The Hermes relayer
has made a monumental contribution toward the success of IBC and Cosmos, and it
is the most widely used IBC relayer in the Cosmos ecosystem today.

The adoption of Interchain and IBC continues to grow, and IBC traffic is
increasing at an exponential pace. From our experience in developing and
operating the Hermes relayer, we have learned many valuable lessons about
the challenges of building a reliable IBC relayer for a modern Interchain
ecosystem.

In this section, we will share some of the challenges that the v1 Hermes
relayer faces, and the motivation for why there is a need to rethink about
the IBC relayer architecture.

### Support for non-SDK and non-Cosmos Chains

The success of IBC and the growth of Interchain introduce new use cases that
the v1 relayer did not sufficiently focus on. For example, we have received
many feature requests from Substrate to modify the Hermes code base to better
support relaying between a Cosmos chain and a Substrate chain.

## Support for mutiple versions of Cosmos chain


## Support for multiple batching strategies


## Async Concurrency


## Type safety for differentiation of identifiers from different chains

## Code correctness and formal verification


# Decision

## Development Strategy

The Hermes v2 relayer is designed from the top down with a new architecture
that is compatible with the existing code base. This reduces the risk of having
a complete rewrite from the ground up, which may take too long and may fail
to deliver.

We progress toward the relayer v2 design with an MVP, called relayer v1.5,
which adds a small number of experimental features to the existing v1 relayer
without replacing existing features of the v1 relayer. In contrast, a v2
relayer is expected to supercede the majority of features of the v1 relayer
with new and improved code.

For the purpose of the architecture re-design, all the new code being
developed are targeted toward the relayer v2. But the new code will be
usable in the form of experimental features when the relayer v1.5 is
released. Both the v1 relayer and the new relayer will co-exist from
v1.5 onward, until the v2 relayer is released.

In the relayer v1.5 MVP, the new relayer only re-implements the packet
worker and the transaction sender. With that, the new relayer does not
depend on the
[`RelayPath`](ibc_relayer::link::RelayPath) and
[`Link`](ibc_relayer::link::Link) data types, as well as the `send_tx`
methods in the v1 relayer. In contrast, the new relayer will initially
continue to rely on the
[`ForeignClient`](ibc_relayer::foreign_client::ForeignClient) and
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) datatypes
to perform queries and processing of messages.

## Architecture Overview

A full description of the relayer v2 architecture is too much to be described
in this ADR. Instead, readers are encouraged to read the full documentation
from the generated Cargo docs for the new relayer crates.

At its core, the v2 relayer makes use of a new programming technique, called
_context-generic programming_ (CGP), to implement the relayer components in a
modular fashion. CGP turns OOP methods into modular components by replacing
the concrete `Self` type with a _generic_ `Context` type. Using the special
properties of Rust's trait system, CGP allows component implementations to
add new constraints and requirements to the `Context` type through `where`
clauses inside `impl` blocks, by which the constraints would automatically
propagate to the top level without having to repeatedly specify the
constraints at every level of the code.

### Relayer Framework

Using CGP, the core logic of the new relayer is implemented as a fully
abstract library crate called [`ibc-relayer-framework`](ibc_relayer_framework),
with no dependency on external crates except for using the
[`async-trait`](async_trait) crate to support
async functions inside traits. In addition, the relayer framework is
developed with `#![no_std]` enabled. By having almost no external dependencies,
the relayer can be ported to various restrictive environments, such as
Wasm, the Substrate runtime, and symbolic execution environments.

Since the relayer framework is fully abstract, it also does not depend on
the concrete type definitions of the IBC constructs, including primitives
like height. Instead, the types are declared as abstract associated types in
traits like
[`HasChainTypes`](ibc_relayer_framework::base::chain::traits::types::HasChainTypes)
and [`HasRelayTypes`](ibc_relayer_framework::base::relay::traits::types::HasRelayTypes):

```rust,ignore
trait HasChainTypes {
    type Height;
    type Timestamp;
    type Message;
    type Event;
    /* ... */
}

trait HasRelayTypes {
    type SrcChain: HasChainTypes;
    type DstChain: HasChainTypes;
    type Packet;
    /* ... */
}
```

Readers are encouraged to refer to the documentation and source code for
the [`ibc-relayer-framework`](ibc_relayer_framework) crate to see the full definitions.
Since the type definitions are abstract, different chain implementations
are free to make use of custom types to instantiate the relayer
with. For example, a Cosmos chain implementation can use a `Height` type
that contains a revision number, while a mock chain implementation can use
`u64` as height.

The use of abstract types is most useful in places where chain implementations
need different concrete types by necessity, such as the types for message,
event, consensus state, and signer keys. In relayer v1, if users need to
customize the implementation of these types, they would typically have to
submit a pull request to apply the changes to everyone, or keep a long fork of
the relayer code. With relayer v2, a Cosmos relayer can use only Cosmos-specific
types, without having to customize the types to handle non-Cosmos use cases.

The use of abstract types also solves the problem of having multiple versions
of protobuf definitions for different versions of Cosmos chains. In relayer v1,
the message types are tightly coupled with the protobuf definitions generated
in [`ibc-proto`](ibc_proto) and
[`tendermint-proto`](tendermint_proto). In relayer v2, it is possible to have
multiple versions of the generated protobuf modules to co-exist, and implement
different versions of relayers for different versions of Cosmos chains. Although
this would still result in code duplication in the Cosmos-specific
implementations, the duplication would only involve low-level operations such as
protobuf encodings, and it would not affect the core logic of the relayer or
other users of the relayer framework.

### Update client message builder

The use of CGP allows the relayer framework to break down complex relaying
logic into smaller pieces of components. As an example, the component
for building UpdateClient messages have the following trait:

```rust,ignore
pub trait UpdateClientMessageBuilder<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn build_update_client_messages(
        context: &Relay,
        _target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Relay::Error>;
}
```

The trait allows an update client message builder component to be implemented
generically over a relay context `Relay` and a chain target `Target` (for targetting either the source or destination chain). Using that, we can
for example define a
[`SkipUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::skip_update_client::SkipUpdateClient)
component as follows:

```rust,ignore
pub struct SkipUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

impl<Relay, Target>
    UpdateClientMessageBuilder<Relay, Target>
    for SkipUpdateClient<InUpdateClient>
where /* ... */
{ /* ... */ }
```

The
[`SkipUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::skip_update_client::SkipUpdateClient)
component is a _middleware_ component that wraps around
an inner update client message builder, and skips calling the inner component
if it finds that a client update at the given height had already been done
before on the target chain.

The trait also allows an update client message builder component to be
implemented with a concrete relay context, such as a Cosmos-specific
update client message builder:

```rust,ignore
pub struct BuildCosmosUpdateClientMessage;

impl<Target>
    UpdateClientMessageBuilder<CosmosRelayContext, Target>
    for BuildCosmosUpdateClientMessage
where /* ... */
{ /* ... */ }
```

The component `BuildCosmosUpdateClientMessage` is implemented to work with
a concrete relay context `CosmosRelayContext`, so it cannot be used with
other non-Cosmos relay contexts. However, it can be composed with other
generic components like
[`SkipUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::skip_update_client::SkipUpdateClient)
and form a component like:

```rust,ignore
type ChosenUpdateClientMessageBuilder =
    SkipUpdateClient<WaitUpdateClient<
        BuildCosmosUpdateClientMessage>>;
```

Above we have a declarative type alias of a component `ChosenUpdateClientMessageBuilder`, which is composed of
three smaller components. When this is used, the component will first use
[`SkipUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::skip_update_client::SkipUpdateClient)
to check whether the client has already been updated, it then uses
[`WaitUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::wait_update_client::WaitUpdateClient)
to wait for the counterparty chain's height
to increase beyond the target height, then uses `BuildCosmosUpdateClientMessage`
to build the Cosmos-specific update client message.

Having generic components like
[`SkipUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::skip_update_client::SkipUpdateClient)
and
[`WaitUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::wait_update_client::WaitUpdateClient)
means that a context-specific component like `BuildCosmosUpdateClientMessage` can
opt to focus on only implementing the low-level logic of building a
Cosmos-specific UpdateClient message. On the other hands, users of the relayer
framework can also _opt-out_ of using a middleware component like
[`WaitUpdateClient`](ibc_relayer_framework::base::relay::impls::messages::wait_update_client::WaitUpdateClient),
or they can also define new middleware components
to customize the UpdateClient logic.

### IBC message sender

A use case for having modular components is the ability for relayers to customize
on different strategies for sending IBC messages. For instance, a message sender
for a minimal relayer can be:

```rust,ignore
type MinimalIbcMessageSender =
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
```

The `MinimalIbcMessageSender` decleared above uses
[`SendIbcMessagesWithUpdateClient`](ibc_relayer_framework::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
to prepend UpdateClient messages to the front of messages being sent, and
[`SendIbcMessagesToChain`](ibc_relayer_framework::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain)
sends the messages from the relay context to the chain context.

On the other hand, in a full-featured relayer, a batch message worker could be
used to batch multiple messages being sent within a timeframe into a
single message batch:

```rust,ignore
type FullIbcMessageSender = SendMessagesToBatchWorker;

type IbcMessageSenderForBatchWorker =
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
```

In the above declaration, the relay context would use
[`SendMessagesToBatchWorker`](ibc_relayer_framework::full::batch::message_sender::SendMessagesToBatchWorker)
to send the IBC messages to the batch worker using an MPSC channel. Inside
the batch worker, it would then bundle multiple batches of messages and
send them together using
`SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>`. Through this, the
batched version of the message sender can save cost and performance on sending
IBC messages, because the relayer would only attach one UpdateClient message
alongside multiple messages that are batched together.

With the declarative nature of context-generic programming, users would be able
to easily customize on different strategies of sending IBC messages,
as well as building update client messages. CGP also helps propagate the
additional constraints of components to the concrete context implementer.
For instance, if
[`SendMessagesToBatchWorker`](ibc_relayer_framework::full::batch::message_sender::SendMessagesToBatchWorker)
is used, the relay context is
required to provide MPSC channels that can be used for sending messages to the
batch worker. On the other hand, if only `MinimalIbcMessageSender` is used,
the relay context can remove the burden of having to provide an MPSC channel.

### Async Concurrency

The v1 relayer was developed at a time when Rust's async/await infrastructure
was not yet ready for use. As a result, the v1 relayer uses thread-based
concurrency, by spawning limited number of threads and manually multiplexing
multiple tasks in each thread.

As time moves forward, the async/await feature in Rust has become mature enough,
and the new relayer is able to make use of async tasks to manage the concurrency
for relaying packets. At its core, the relaying of packets is done through the
following interface:

```rust,ignore
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) ->
        Result<(), Relay::Error>;
}
```

The
[`PacketRelayer`](ibc_relayer_framework::base::relay::traits::packet_relayer::PacketRelayer)
trait allows the handling of a single IBC packet at a time.
When multiple IBC packets need to be relayed at the same time, the relayer
framework allows multiple async tasks to be spawned at the same time, with each
task sharing the same relay context but doing the relaying for different packets.

To optimize for efficiency, the relay context can switch the strategy for
batching messages and transactions at the lower layers without affecting the
logic for the packet relayers themselves. From the perspective of the packet
relayer implementation, the relay context appears to be exclusively owned by the
packet relayer, and it is not aware of other concurrent tasks running.

The relayer framework uses multiple layers of optimizations to improve the
efficiency of relaying IBC packets. The first layer performs message
batching per relay context, by collecting messages being sent over a relay
context within a time frame and sending them all as a single batch if it does not
exceed the batch size limit. This layer does the batching per relay context,
because it allows the use of the
[`SendIbcMessagesWithUpdateClient`](ibc_relayer_framework::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
component to
add update client messages to the batched messages, which has to be tied to a
specific relay context.

The second layer performs message batching per chain context. It would collect
all messages being sent to a chain within a time frame, and send them all in
a single batch if it does not exceed the batch size limit. The batching
mechanics are the same, but is done at the chain level, as opposed to at the relayer level.
As a result, it is able to batch IBC messages coming from multiple counterparty chains.

The third layer performs batching at the _transaction_ context. It provides a
_nonce allocator_ interface to allow a limited number of messages to be sent
at the same time as other transactions. Since Cosmos chains require strict order in
the use of monotonically-increasing account sequences as nonces, the nonce
allocator needs to be conservative in the number of nonces to be allocated in
parallel. This is because if an earlier transaction failed to be broadcasted,
later transactions that use the higher-numbered nonces may fail as well. When
a nonce mismatch error happens, the nonce allocator also needs to be smart
enough to refresh the cached nonce sequences so that the correct nonces can be
allocated to the next messages.

It is also worth noting that all optimization layers offered by the relayer
framework are _optional_. For example, if the relayer is used to relay
non-Cosmos chains, or if future Cosmos SDK chains allow parallel nonces to be
used, then one can easily swap with a different nonce allocator that is better
suited for the given nonce logic. The relayer framework also provides a _naive_
nonce allocator, which only allows one transaction to be sent at a time using
a mutually exclusive nonce.

The relayer framework also allows for easy addition of new optimization layers.
For example, we can consider adding a _signer allocator_ layer, which
multiplexes the sending of parallel transactions using multiple signer wallets.
Adding such a layer would require transaction contexts that use it to provide
a _list_ of signers, as compared to a single signer. On the other hand,
transaction contexts that do not need such an optimization are not affected and
would only have to provide a single signer.

### Error Handling

With the async task-based concurrency, the new relayer has simpler error
handling logic than the v1 relayer. At minimum, there are two places where retry
logic needs to be implemented. The first is at the packet relayer layer, where
if any part of the relaying operation fails, the packet relayer will retry
the whole process of relaying that packet. This is done by having a separate
[`RetryRelayer`](ibc_relayer_framework::full::relay::impls::packet_relayers::retry::RetryRelayer)
component that specifically handles the retry logic:

```rust,ignore
type ChosenPacketRelayer = RetryRelayer<FullCycleRelayer>;
```

In the above example, the
[`FullCycleRelayer`](ibc_relayer_framework::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer)
is the core packet relayer that
performs the actual packet relaying logic. It is wrapped by
[`RetryRelayer`](ibc_relayer_framework::full::relay::impls::packet_relayers::retry::RetryRelayer),
which calls `FullCycleRelayer::relay_packet()` in an attempt to relay the
IBC packet. If the operation fails and returns an error,
[`RetryRelayer`](ibc_relayer_framework::full::relay::impls::packet_relayers::retry::RetryRelayer)
checks on whether the error is retryable, and if so it calls the inner
relayer again. As the relayer framework also keeps the error type generic,
a concrete relay context can provide custom error types as well as provide
methods for the
[`RetryRelayer`](ibc_relayer_framework::full::relay::impls::packet_relayers::retry::RetryRelayer)
to determine whether an error is retryable.

Inside the
[`FullCycleRelayer`](ibc_relayer_framework::base::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer),
it always starts the relaying from the beginning
of the packet lifecycle, which is to relay a `RecvPacket`, then an `AckPacket` or
a `TimeoutPacket`. It does not check for what is the current relaying state of the
packet, because this is done by separate components such as
[`SkipReceivedPacketRelayer`](ibc_relayer_framework::base::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer),
which would skip relaying a `RecvPacket` if the chain
has already received the packet before. This helps keep the core relaying logic simple,
while still providing a robust retry mechanism that allows the retry operation
to resume at an appropriate stage.

The second layer of the retry logic is at the transaction layer with the nonce allocator.
When sending of a transaction fails, the nonce allocator can check whether
the failure is caused by nonce mismatch errors. If so, it can retry sending
the transaction with a refreshed nonce, without having to propagate the error
all the way back to
[`RetryRelayer`](ibc_relayer_framework::full::relay::impls::packet_relayers::retry::RetryRelayer).

### Model Checking

The retry logic at the transaction layer can be more complicated than one
imagines. This is because failure of sending transactions may be local and
temporary, and the relayer may receive transaction failures even if a transaction
is eventually committed, such as due to insufficient waiting time before timing
out, or failure on the full node or network while the transaction has already
been broadcasted. If the sending of a successful transaction is incorrectly
identified as a failure, it may result in cascading failures being accumulated
in the relayer, such as repeatedly retrying the sending of transactions with
invalidated nonces.

Because of this, a lot of rigorous testing is required to ensure that the
combined logic of retrying to send packets and transactions is sound. A good
way to test that is to build a model of the concurrent system and test all
possible states using model checking tools like
[TLA+](https://lamport.azurewebsites.net/tla/tla.html) and
[Apalache](https://apalache.informal.systems/).
On the other
hand, since the relayer framework itself is fully abstract, it is also possble
to treat the relayer framework as a model. This can be potentially done by using
model checking tools for Rust, such as
[Kani](https://github.com/model-checking/kani) and
[Prusti](https://github.com/viperproject/prusti-dev). If that is possible,
it could significantly reduce the effort of model checking, since there
wouldn't be a need to re-implement the relayer logic in a separate language.

Although we are still in the research phase of exploring the feasibility of
doing model checking in Rust, the abstract nature of the relayer framework
increases the chance of the tools being a good fit. In particular, the
relayer framwork supports `no_std` and is not tied to a specific async runtime.
As a result, fewer problems arise in a symbolic execution environment like Kani,
which does not support std and async constructs.

### All-In-One Traits

The relayer framework makes use of context-generic programming to define
dozens of component interfaces and implementations. Although that provides a
lot of flexibility for context implementers to mix and match components as
they see fit, it also requires them to have a deeper understanding of how
each component works and how to combine them using context-generic programming.

As an analogy, a computer is made of many modular components, such as CPU, RAM,
and storage. With well-defined hardware interfaces, anyone can, in theory,
assemble their own computer with the exact hardware specs that they prefer.
However, even though having modular hardware components is very useful, the
majority of consumers would prefer _not_ to assemble their own computer, or to
understand how each hardware component works. Instead, consumers prefer to have
pre-assembled computers that are designed to fit specific use cases, such as
gaming laptops or smartphones with good cameras, and choose a model that matches
closest to their use cases.

To help normal users to build custom relayers with minimal effort, the relayer
framework offers _all-in-one_ traits that have most parts of the relayer
pre-configured as _presets_. The relayer framework currently offers two presets:
minimal and full-featured.

The minimal preset, as its name implies, offers an abstract implementation of a
minimal relayer, which only performs the core logic of relaying with no
additional complexity. Because the relayer is minimal, there are fewer requirements
that the concrete contexts need to implement. As a result, it takes the least
effort for users to build a minimal relayer that targets custom chains like
solomachines, or custom environments like Wasm.

On the other hand, the full preset includes all available components that the
relayer framework offers, such as message batching, parallel transactions,
packet filtering, retrying of errors, and telemetry. While these features are not
essential for a minimal relayer to work, they are useful for operating
production relayers that require high reliability and efficiency. As a tradeoff,
since the full relayer includes more components with complex logic, it also
imposes more requirements on the concrete context implementation, and there may
be more potential for subtle bugs to be found.

The minimal preset requires implementers of custom relay contexts to implement
the _one-for-all_ traits such as
[`OfaBaseChain`](ibc_relayer_framework::base::one_for_all::traits::chain::OfaBaseChain)
and
[`OfaBaseRelay`](ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay).
In addition
to that, the full preset requires implementers to also implement traits like
[`OfaFullChain`](ibc_relayer_framework::full::one_for_all::traits::chain::OfaFullChain)
and
[`OfaFullRelay`](ibc_relayer_framework::full::one_for_all::traits::relay::OfaFullRelay).
An example use of this is demonstrated
in the later section using the Cosmos chain context.

### Limitations of All-In-One Traits

Since the relayer framework only offers two presets, there is a gap between
the minimal preset and the full preset. As a result, users cannot selectively
choose only specific features from the full relayer, such as enabling only
the message batching feature without telemetry. The choice of us imposing
these restrictions is _deliberate_, as we want to keep the all-in-one traits
simple and have a smooth learning curve.

It is worth noting that even though the relayer components defined using
context-generic programming are fully modular, the all-in-one traits are
designed to be _rigid_ and _specialized_. Observant readers may notice that
the all-in-one traits are similar to the traditional god traits that are
commonly found in Rust code, such as
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) in relayer v1.
At the expense of user convenience, the all-in-one traits suffer the same
limitations as other
god traits of being very complex and inflexible. However, the main difference is
that the all-in-one traits are nothing but glue code around the actual
components, hence their presence is optional and can be bypassed easily if
needed.

If users want to mix and match specific features of the relayer, they can
instead bypass the all-in-one traits and use the relayer components directly
with CGP. Similarly, if users want to implement custom components, such as
custom logic for building UpdateClient messages, they should skip the all-in-one
traits and implement the custom logic directly using CGP.

In the future, the relayer framework may offer more variants of all-in-one
traits that are catered for specific use cases. For example, we may define
multiple specialized relayers that _prioritize_ differently on how packets
should be relayed, such as based on incentivized packet fees or how long the
packet has stayed idle.

### Cosmos Relayer

The all-in-one traits offered by the relayer framework serves as a starter
pack for building custom relayers. To dogfood the all-in-one traits, we create
the [`ibc-relayer-cosmos`](crate) crate which offers the Cosmos-specific
implementation of the relayer.

Following the available all-in-one presets, the [`ibc-relayer-cosmos`](crate)
crate offers two variants of Cosmos chains, minimal and full, defined as follows:

```rust,ignore
pub struct MinCosmosChainContext {
    pub handle: ChainHandle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
}

pub struct FullCosmosChainContext {
    pub handle: ChainHandle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_channel: CosmosBatchChannel,
    pub telemetry: CosmosTelemetry,
}
```

Compared to the
[`MinCosmosChainContext`](crate::contexts::min::chain::MinCosmosChainContext),
the [`FullCosmosChainContext`](crate::contexts::full::chain::FullCosmosChainContext)
contains two additional fields, `batch_channel` and `telemetry`.
This is because the full
preset makes use of the batched message sender and telemetry components, which
requires the chain context to provide the batch channels and telemetry context.
Hence, if a user wants to use the full-featured Cosmos relayer, they would also
have to instantiate and provide the additional parameters when constructing the
chain context.

The Cosmos chain context is implemented as an MVP for the relayer v1.5. As a
result, it delegates most of the chain operations to the existing
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle)
code in relayer v1. As we progress toward the v2 relayer, the Cosmos chain
context is expected to eventually remove its dependency on
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) and
directly hold low-level fields such as `grpc_address`.

To make use of the Cosmos chain context for relaying between Cosmos chains,
we implement the one-for-all traits for our Cosmos chain contexts roughly as
follows:

```rust,ignore
impl OfaBaseChain for MinCosmosChainContext
{
    type Preset = MinimalPreset;

    type Error = CosmosError;

    type Height = CosmosHeight;

    type Timestamp = CosmosTimestamp;

    type Message = CosmosMessage;

    type Event = CosmosEvent;

    type ChainStatus = CosmosChainStatus;

    /* ... */

    async fn query_chain_status(&self) -> Result<CosmosChainStatus, CosmosError> {
        /* ... */
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosMessage>,
    ) -> Result<Vec<Vec<CosmosEvent>>, CosmosError> {
        /* ... */
    }

    /* ... */
}
```

For demonstration purposes, the above code is slightly simplified from the actual
Cosmos chain implementation. Readers are encouraged to refer to the
[`ibc-relayer-cosmos`](crate) itself to see the full implementation details.

In the
[`OfaBaseChain`](ibc_relayer_framework::base::one_for_all::traits::chain::OfaBaseChain)
implementation for
[`MinCosmosChainContext`](crate::contexts::min::chain::MinCosmosChainContext),
we first
define the `Preset` type attribute to
[`MinimalPreset`](ibc_relayer_framework::base::one_for_all::presets::MinimalPreset),
indicating that we
only want to build a minimal relayer with our concrete context. We then bind
the abstract types such as `Error` and `Height` to the Cosmos-specific types
such as `CosmosError` and `CosmosTimestamp`. Finally, we implement the abstract
methods that are required to be provided by the concrete chain implementation,
such as `query_chain_status` and `send_messages`.

We would also do the same implementation for the concrete relay contexts, such
as implementing
[`OfaBaseRelay`](ibc_relayer_framework::base::one_for_all::traits::relay::OfaBaseRelay)
for [`MinCosmosRelayContext`](crate::contexts::min::relay::MinCosmosRelayContext),
which would contain two
[`MinCosmosChainContext`](crate::contexts::min::chain::MinCosmosChainContext)s.
Once the traits are implemented, the relayer
methods would automatically be implemented by wrapping the relay context
inside
[`OfaRelayWrapper`](ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper),
such as follows:

```rust,ignore
let relayer = OfaRelayWrapper::new(MinCosmosRelayContext::new(/* ... */));
let packet = /* ... */;

// PacketRelayer::relay_packet is automatically implemented
relayer.relay_packet(packet);
```

The wrapper types like
[`OfaRelayWrapper`](ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper)
are newtype wrappers that help provide
automatic implementation of the relayer traits provided by the relayer framework.
The reason it is needed is to avoid having conflicting trait implementations
if we try to implement it without the wrapper types. Aside from that, the two
steps of implementing the one-for-all traits and then wrapping the values inside
the one-for-all wrappers are sufficient for us to build a fully customized
relayer from the relayer framework.

## Development plan toward relayer v1.5

We are slowly progressing toward finishing the relayer v1.5 MVP. At the current
stage, we have finished a full implementation of the
[`PacketRelayer`](ibc_relayer_framework::base::relay::traits::packet_relayer::PacketRelayer)
and tested the successful relaying of a single IBC packet for Cosmos chains.
To make the code ready for an initial v1.5 MVP release, the following work still
needs to be completed:

### IBC Event Source

To support relaying of multiple packets, the relayer framework needs to define
an event source interface to listen to incoming IBC packets and then spawn
new tasks to relay the packets using
[`PacketRelayer`](ibc_relayer_framework::base::relay::traits::packet_relayer::PacketRelayer).
The Cosmos MVP for this
will make use of the event subscription code provided by the v1 relayer
supervisor to implement the event source.

### Transaction Context

The current MVP makes use of the existing
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle)'s `send_messages` method
to submit messages as transactions to the chain. In order to implement custom
strategies for submitting transactions, we are implementing a new transaction
context as an additional layer below the chain context to handle the submission
of messages as transactions to the blockchain.

Due to the v2 relayer having different concurrency semantics from the v1 relayer,
most of the messages sent by the new relayer would get queued up and be sent
sequentially if they are sent using the existing
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle). As a result,
the transaction context is needed for the new relayer to demonstrate a measurable
improvement in performance from the v1 relayer.

### CLI Integration

The new relayer will be made available by adding it as an experimental
subcommand in the current relayer CLI. For example, the following CLI could
be introduced to start the new relayer:

```bash
hermes new-relay start
```

The new relayer CLI would have to implement the logic for loading the relayer
config in the current format, and then constructing the Cosmos relay context
based on that.

The initial new relayer MVP would initially lack many features from the current
v1 relayer, such as packet clearing, robust retry logic, and handshakes. As a
result, it is meant to be experimental and not used in production. The CLI
may be conditionally enabled from an `experimental` feature flag, so that
official releases of the Hermes relayer do not expose the CLI to be accidentally
used by relayer operators.

## Development plan toward relayer v2

To progress the relayer v1.5 MVP toward relayer v2, there are several key
milestones that we need to reach:

### Remove Dependency on [`ForeignClient`](ibc_relayer::foreign_client::ForeignClient)

The relayer v1.5 MVP currently relies on
[`ForeignClient`](ibc_relayer::foreign_client::ForeignClient) to perform operations
such as building UpdateClient messages. As a tradeoff, this restricts the
Cosmos relay context to be usable with two Cosmos chains. To support relaying
between a Cosmos chain and a non-Cosmos chain, it is necessary to remove
the dependency on
[`ForeignClient`](ibc_relayer::foreign_client::ForeignClient),
as non-Cosmos chains would otherwise
have to implement
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle)
in order to support the heterogenous relaying.

### Remove Dependency on [`ChainHandle`](ibc_relayer::chain::handle::ChainHandle)

The relayer v1.5 MVP currently relies on
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) for the majority of chain
operations, such as performing queries and building merkle proofs. However as
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) has a thread-based
concurrency, it can only handle one operation
at a time. With the transaction context, the new relayer is able to parallelize
the query operations from the sending of transactions. However, the query
part of the chain remains a bottleneck, and may impact the performance of the
new relayer.

As a result, the new Cosmos relayer needs to remove its dependency on
[`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) so that it can perform
concurrent queries to the chain. This
would also allow the relayer framework to implement proper caching layers
to reduce the traffic on the full node.

### Heterogenous Relaying MVP

The new relayer needs to demonstrate that the new architecture is sufficient
to support relaying between different types of chains, such as Cosmos to
Substrate relaying. To show that, we need to implement at least one non-Cosmos
chain context and implement a relay context that supports two different
chain contexts.

An MVP candidate for heterogenous relaying is to build a mock solomachine chain
context. Because the solomachine spec is relatively simple, it should require
less effort to build a solomachine chain context from scratch. Furthermore,
as the solomachine light client is already officially supported in ibc-go,
we can test solomachine relaying without having to use a custom Cosmos chain
with custom light clients.

Once the mock solomachine chain context is implemented, it would be possible to
write integration tests to relay IBC packets between an in-memory solomachine
with a live Cosmos chain.

### Multiple Strategies for Concurrent Transactions

A key goal for relayer v2 is to support the submission of concurrent
transactions with upcoming major changes for Cosmos chains, in particular
prioritized mempool and ABCI++. Depending on the chain implementation,
it may not be possible to submit parallel transactions with different nonces.

To mitigate this, the relayer may need different strategies for allocating nonces.
For example, future Cosmos SDK chains may offer parallel lanes of account
sequences, so that parallel transactions can make use of nonces from different
lanes.

An alternative strategy would be to multiplex the sending of transactions between
multiple signers. However, as this may impose an operational burden on relayer
operators, the relayer may need to automate the process of managing multiple
wallets, such as with the use of the fee grant module.

The relayer v1.5 MVP offers a nonce allocator interface as a starting point for
implementing different nonce allocation strategies. However, it currently
only implements a naive nonce allocator which does _not_ support parallel
transactions. In contrast, the relayer v2 would need to have multiple nonce
allocators implemented, and test them thoroughly with new versions of
Cosmos chains.

The relayer v1.5 MVP will not expose interfaces that support sending
transactions with multiple signers. Since such features also require significant
effort in the form of proper UX design, it is left as a task for relayer v2 to implement.

# Status

Proposed

# Consequences

# Positive

# Negative

# Neutral

# References
