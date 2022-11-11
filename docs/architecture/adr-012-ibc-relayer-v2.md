# ADR 012: New Relayer Architecture

# Changelog

* 2022-11-10: Initial Draft

# Context and Problem Statement

The current Hermes relayer, hereby called V1 relayer in this document, was
implemented at a time when the Cosmos ecosystem was still very new, and the
idea of cross-chain with IBC was still a novel concept. The Hermes relayer
has a monumental contribution toward the success of IBC and Cosmos, and it
is the most widely used IBC relayer in the Cosmos ecosystem today.

The adoption of Interchain and IBC continues to grow, and IBC traffic is
increasing at an expoential pace. From our experience in developing and
operating the Hermes relayer, we have learned many valuable lessons about
the challenges of building a reliable IBC relayer for a modern Interchain
ecosystem.

In this section, we will share some of the challenges that the V1 Hermes
relayer faces, and the motivation for why there is a need to rethink about
the IBC relayer architecture.

### Support for non-SDK and non-Cosmos Chains

The success of IBC and the growth of Interchain introduce new use cases that
the V1 relayer did not sufficiently focus on. For example, we have received
many feature requests from Substrate to modify the Hermes code base to better
support relaying between a Cosmos chain and a Substrate chain.

## Support for mutiple versions of Cosmos chain


## Support for multiple batching strategies


## Async Concurrency


## Type safety for differentiation of identifiers from different chains

## Code correctness and formal verification


# Decision

## Development Plan

The Hermes V2 relayer is designed from the top down with a new architecture
that is compatible with existing code base. This reduces the risk of having
a complete rewrite from the ground up, which may take too long and may fail
to deliver.

We progress toward the relayer v2 design with an MVP, called relayer v1.5,
which adds a small number of experimental features to the existing v1 relayer
without replacing existing features of the v1 relayer. In contrast, a v2
relayer is expected to supercede the majority features of the v1 relayer
with new and improved code.

For the purpose of the architecture re-design, all the new code being
developed are targetted toward the relayer v2. But the new code will be
usable in the form of experimental features when the relayer v1.5 is
released. Both the v1 relayer and the new relayer will co-exist from
v1.5 onward, until the v2 relayer is released.

In the relayer v1.5 MVP, the new relayer only re-implements the packet
worker and the transaction sender. With that, the new relayer does not
depend on the `RelayPath` and `Link` data types, as well as the `send_tx`
methods in the v1 relayer. In contrast, the new relayer will initially
continue to rely on the `ForeignClient` and `ChainHandle` datatypes
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
propagated to the top level without having to repeatedly specify the
constraints at every level of the code.

### Relayer Framework

Using CGP, the core logic of the new relayer is implemented as a fully
abstract library crate called `ibc-relayer-framework`, with no dependency
to external crates except for using the `async-trait` crate to support
async functions inside traits. In addition, the relayer framework is
developed with `#![no_std]` enabled. By having almost no external dependency,
the relayer can be ported to various restrictive environments, such as
Wasm, Substrate runtime, and symbolic execution environments.

Since the relayer framework is fully abstract, it also does not depends on
the concrete type definitions of the IBC constructs, including primitives
like height. Instead, the types are declared as abstract associated types in
traits like `HasChainTypes` and `HasRelayTypes`:

```rust
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
the `ibc-relayer-framework` crate to see the full definitions.
Since the type definitions are abstract, different chain implementations
are free to make use of custom types to instantiate the relayer
with. For example, a Cosmos chain implementation can use a `Height` type
that contains revision number, while a mock chain implementation can use
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
in `ibc-proto` and `tendermint-proto`. In relayer v2, it is possible to have
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

```rust
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
for example define a `SkipUpdateClient` component as follows:

```rust
pub struct SkipUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

impl<Relay, Target>
    UpdateClientMessageBuilder<Relay, Target>
    for SkipUpdateClient<InUpdateClient>
where /* ... */
{ /* ... */ }
```

The `SkipUpdateClient` component is a _middleware_ component that wraps around
an inner update client message builder, and skips calling the inner component
if it finds that a client update at the given height had already been done
before on the target chain.

The trait also allows an update client message builder component to be
implemented with a concrete relay context, such as a Cosmos-specific
update client message builder:

```rust
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
generic components like `SkipUpdateClient` and form a component like:

```rust
type ChosenUpdateClientMessageBuilder =
    SkipUpdateClient<WaitUpdateClient<
        BuildCosmosUpdateClientMessage>>;
```

Above we have a declarative type alias of a component `ChosenUpdateClientMessageBuilder`, which is made from the composition of
three smaller components. When this is used, the component will first
use `SkipUpdateClient` to check whether the client has already been updated,
it then uses `WaitUpdateClient` to wait for the counterparty chain's height
to increase beyond the target height, then uses `BuildCosmosUpdateClientMessage`
to build the Cosmos-specific update client message.

Having generic components like `SkipUpdateClient` and `WaitUpdateClient` means
that a context-specific component like `BuildCosmosUpdateClientMessage` can
opt to focus on only implementing the low-level logic of building a
Cosmos-specific UpdateClient message. On the other hands, users of the relayer
framework can also _opt-out_ of using a middleware component like
`WaitUpdateClient`, or they can also define new middleware components
to customize the UpdateClient logic.

### IBC message sender

A use case for having modular component is the ability for relayers to customize
on different strategies for sending IBC messages. For instance, a message sender
for a minimal relayer can be:

```rust
type MinimalIbcMessageSender =
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
```

The `MinimalIbcMessageSender` decleared above uses
`SendIbcMessagesWithUpdateClient` to prepend UpdateClient messages to
the front of messages being sent, and `SendIbcMessagesToChain` sends
the messages from the relay context to the chain context.

On the other hand, in a full-featured relayer, a batch message worker could be
used to batch multiple batch of messages being sent within a timeframe into a
single message batch:

```rust
type FullIbcMessageSender = SendMessagetoBatchWorker;

type IbcMessageSenderForBatchWorker =
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
```

In the above declaration, the relay context would use `SendMessagetoBatchWorker`
to send the IBC messages to the batch worker using an MPSC channel. Inside
the batch worker, it would then bundle multiple batches of messages and
send them together using
`SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>`. Through this, the
batched version of the message sender can save cost and performance on sending
IBC messages, because the relayer would only attach one UpdateClient message
along multiple messages that are batched together.

With the declarative nature of context-generic programming, users would be able
to easily customize on different strategies of sending IBC messages,
as well as building update client messages. CGP also helps propagate the
additional constraints of components to the concrete context implementer.
For instance, if `SendMessagetoBatchWorker` is used, the relay context is
required to provide MPSC channels that can be used for sending messages to the
batch worker. On the other hand, if only `MinimalIbcMessageSender` is used,
the relay context can remove the burden of having to provide an MPSC channel.

### Async Concurrency

The v1 relayer was developed at a time when Rust's async/await infrastructure
was not yet ready for use. As a result, the v1 relayer uses thread-based
concurrency, by spawning limited number of threads and does manual multiplexing
of multiple tasks in each thread.

As time moves forward, the async/await feature in Rust has become mature enough,
and the new relayer is able to make use of async tasks to manage the concurrency
for relaying packets. At its core, the relaying of packets is done through the
following interface:

```rust
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) ->
        Result<(), Relay::Error>;
}
```

The `PacketRelayer` trait allows the handling of a single IBC packet at a time.
When multiple IBC packets need to be relayed at the same time, the relayer
framework allows multiple async tasks to be spawned at the same time, with each
tasks sharing the same relay context but does the relaying for different packets.

To optimize for efficiency, the relay context can switch the strategy for
batching messages and transactions at the lower layers without affecting the
logic for the packet relayers themselves. From the perspective of the packet
relayer implementation, the relay context appears to be exclusively owned by the
packet relayer, and it is not aware of other concurrent tasks running.

The relayer framework uses multiple layers of optimizations to improve the
efficiency of relaying IBC packets. The first layer performs message
batching per relay context, by collecting messages being sent over a relay
context within a time frame and send them all as a single batch if it does not
exceed the batch size limit. This layer does the batching per relay context,
because it allows the use of the `SendIbcMessagesWithUpdateClient` component to
add update client messages to the batched messages, which has to be tied to
specific relay context.

The second layer performs message batching per chain context. It would collect
all messages being sent to a chain within a time frame, and send them all in
a single batch if it does not exceed the batch size limit. The batching
mechanics is the same, but is done at the chain level. As a result, it is able
to batch IBC messages coming from multiple counterparty chains.

The third layer performs batching at the _transaction_ context. It provides a
_nonce allocator_ interface to allow a limited number of messages to be sent
at the same time as transactions. Since Cosmos chains require strict order in
the use of monotonically increasing account sequences as nonces, the nonce
allocator needs to be conservative in the number of nonces to be allocated in
parallel. This is because if an earlier transaction failed to be broadcasted,
latter transactions that use the higher-numbered nonces may fail as well. When
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
Adding such layer would require transaction contexts that use it to provide
a _list_ of signers, as compared to a single signer. On the other hands,
transaction contexts that do not need such optimization are not affected and
would only have to provide a single signer.

### Error Handling

With the async task-based concurrency, the new relayer has a simpler error
handling logic than the v1 relayer. At minimum, there are two places where retry
logic needs to be implemented. The first is at the packet relayer layer, where
if any part of the relaying operation failed, the packet relayer would retry
the whole process of relaying that packet. This is done by having a separate
`RetryRelayer` component that specifically handles the retry logic:

```rust
type ChosenPacketRelayer = RetryRelayer<FullCycleRelayer>;
```

In the above example, the `FullCycleRelayer` is the core packet relayer that
performs the actual packet relaying logic. It is wrapped by `RetryRelayer`,
which would call `FullCycleRelayer::relay_packet()` to attempt to relay the
IBC packet. If the operation fais and returns an error, `RetryRelayer` would
check on whether the error is retryable, and if so it would call the inner
relayer again. As the relayer framework also keeps the error type generic,
a concrete relay context can provide custom error types as well as provide
methods for the `RetryRelayer` to determine whether an error is retryable.

Inside the `FullCycleRelayer`, it always start the relaying from the beginning
of a lifecycle, which is to relay `RecvPacket`, then `AckPacket` or
`TimeoutPacket`. It does not check for what is the current relaying state of the
packet, because this is done by separate components such as
`SkipReceivedPacketRelayer`, which would skip the stage for relaying
`RecvPacket` if the chain has already received the packet before. This helps
keep the core relaying logic simple, while still provides robust retry mechanism
that allows the retry operation to resume at appropriate stages.

The seond layer of retry is at the transaction layer with the nonce allocator.
When sending of a transaction fails, the nonce allocator can check whether
the failure is caused by nonce mismatch errors. If so, it can retry sending
the transaction with a refresh nonce, without having to propagate the error
all the way back to `RetryRelayer`.

### Model Checking

The retry logic at the transaction layer can be more complicated than one
imagine. This is because failure of sending transactions may be local and
temporary, and the relayer may receive transaction failure even if a transaction
is eventually committed, such as due to insufficient waiting time before timing
out, or failure on the full node or network while the transaction has already
been broadcasted. If the sending of a successful transaction is incorrectly
identified as failure, it may result in cascading failures being accumulated
on the relayer, such as repeatedly retrying the sending of transactions with
invalidated nonces.

Because of this, a lot of rigorous testing are required to ensure that the
combined logic of retrying to send packets and transactions is sound. A good
way to test that is to build a model of the concurrent system and test all
possible states using model checking tools like TLA+ and Apalache. On the other
hand, since the relayer framework itself is fully abstract, it is also possble
to treat the relayer framework as a model. This can be potentially done by using
model checking tools for Rust, such as Kani and Prusti. If that is possible,
it could significantly reduce the effort of model checking, since there
wouldn't be need to re-implement the relayer logic in a separate language.

Although we are still in the research phase on exploring the feasibility of
doing model checking in Rust, the abstract nature of the relayer framework
increases the chance of the tools being a good fit. In particular, the
relayer framwork supports no_std and is not tied to specific async runtime.
As a result, it has less problem to work with symbolic execution environments
like Kani, which does not support std and async constructs.

### All-In-One Traits

The relayer framework makes use of context-generic programming to define a
dozens of component interfaces and implementations. Although that provides a
lot of flexibilities for context implementers to mix and match components as
they see fit, it would also require them to have deeper understanding of how
each component works and how to combine them using context-generic programming.

As an analogy, a computer is made of many modular components, such as CPU, RAM,
and storage. With well defined hardware interfaces, anyone can in theory
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
additional complexity. Because the relayer is minimal, it has less requirements
of what the concrete contexts need to implement. As a result, it takes the least
effort for users to build a minimal relayer that targets custom chains like
solomachines, or custom environments like Wasm.

On the other hand, the full preset includes all available components that the
relayer framework offers, such as message batching, parallel transactions,
packet filter, error retry, and telemetry. While these features are not
essential for a minimal relayer to work, they are useful for operating
production relayers that require high reliability and efficiency. As a tradeoff,
since the full relayer includes more components with complex logic, it also
impose more requirements to the concrete context implementation, and there may
be more potential for subtle bugs to be found.

The minimal preset requires implementers of custom relay context to implement
the _one-for-all_ traits such as `OfaBaseChain` and `OfaBaseRelay`. In addition
to that, the full preset requires implementers to also implement traits like
`OfaFullChain` and `OfaFullRelay`. An example use of this is demonstrated
in the later section using the Cosmos chain context.

### Limitations of All-In-One Traits

Since the relayer framework only offers two presets, there is a gap between
the minimal preset and the full preset. As a result, users cannot selectively
choose only specific features from the full relayer, such as enabling only
the message batching feature without telemetry. The choice of us imposing
this restriction is _deliberate_, as we want to keep the all-in-one traits
simple and have a smooth learning curve.

It is worth noting that even though the relayer components defined using
context-generic programming are fully modular, the all-in-one traits are
designed to be _rigid_ and _specialized_. Observant readers may notice that
the all-in-one traits are similar to the traditional god traits that are
commonly found in Rust code, such as `ChainHandle` in relayer v1. At the expense
of user convenience, the all-in-one traits suffer the same limitations as other
god traits of being very complex and inflexible. However, the main difference is
that since the all-in-one traits are nothing but glue code to the actual
components, their presence is optional and can be bypassed easily if needed.

If users want to mix and match specific features of the relayer, they can
instead bypass the all-in-one traits and use the relayer components directly
with context-generic programming. Similarly, if users want to implement custom
components, such as custom logic for building UpdateClient messages, they
should skip the all-in-one traits and implement the custom logic directly using
context-generic programming.

In the future, the relayer framework may offer more variants of all-in-one
traits that are catered for specific use cases. For example, we may define
multiple specialized relayers that _prioritize_ differently on how packets
should be relayed, such as based on incentivized packet fees or how long the
packet has stayed idle.

### Cosmos Relayer

The all-in-one traits offered by the relayer framework serves as a starter
pack for building custom relayers. To dogfood the all-in-one traits, we create
the `ibc-relayer-cosmos` crate which offers the Cosmos-specific implementation
of the relayer.

Following the available all-in-one presets, the `relayer-cosmos` crate offers
two variants of Cosmos chains, minimal and full, defined as follows:

```rust
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

A visual inspection of the type definitions above shows that the full-featured
Cosmos chain context contains two additional fields, `batch_channel` and
`telemetry`. This is because the full preset makes use of the batched message
sender and telemetry components, which requires the chain context to provide
the batch channels and telemetry context. Hence, if a user want to use the
full-featured Cosmos relayer, they would also have to instantiate and provide
the additional parameters when constructing the chain context.

The Cosmos chain context is implemented as an MVP for the relayer v1.5. As a
result, it delegates most of the chain operations to the existing `ChainHandle`
code in relayer v1. As we progress toward the v2 relayer, the Cosmos chain
context is expected to eventually remove its dependency to `ChainHandle`, and
directly holds the low-level fields such as `grpc_address`.

To make use of the Cosmos chain context for relaying between Cosmos chains,
we implement the one-for-all traits for our Cosmos chain contexts roughly as
follows:

```rust
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

For demonstration purpose, the above code is slightly simplified from the actual
Cosmos chain implementation. Readers are encouraged to refer to the
`ibc-relayer-cosmos` itself to see the full implementation details.

In the `OfaBaseChain` implementation for `MinCosmosChainContext`, we first
define the `Preset` type attribute to `MinimalPreset`, indicating that we
only want to build a minimal relayer with our concrete context. We then bind
the abstract types such as `Error` and `Height` to the Cosmos-specific types
such as `CosmosError` and `CosmosTimestamp`. Finally, we implement the abstract
methods that are reqruired to be provided by the concrete chain implementation,
such as `query_chain_status` and `send_messages`.

We would also do the same implementation for the concrete relay contexts, such
as implementing `OfaBaseRelay` for  `MinCosmosRelayContext`, which would contain
two `MinCosmosChainContext`s. Once the traits are implemented, the relayer
methods would automatically be implemented by wrapping the relay context
inside `OfaRelayWrapper`, such as follows:

```rust
let relayer = OfaRelayWrapper::new(MinCosmosRelayContext::new(/* ... */));
let packet = /* ... */;

// PacketRelayer::relay_packet is automatically implemented
relayer.relay_packet(packet);
```

The wrapper types like `OfaRelayWrapper` are newtype wrappers that helps provide
automatic implementation of the relayer traits provided by the relayer framework.
The reason it is needed is to avoid having conflicting trait implementations
if we try to implement it without the wrapper types. Aside from that, the two
steps of implementing the one-for-all traits and then wrapping the values inside
the one-for-all wrappers are sufficient for us to build a fully customized
relayer from the relayer framework.


# Status

Proposed

# Consequences

# Positive

# Negative

# Neutral

# References
