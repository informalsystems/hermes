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

### Modular Components

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
type MyUpdateClientMessageBuilder =
    SkipUpdateClient<WaitUpdateClient<
        BuildCosmosUpdateClientMessage>>;
```

Above we have a declarative type alias of a component `MyUpdateClientMessageBuilder`, which is made from the composition of
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

### All-In-One Traits


### Cosmos Relayer

# Status

Proposed

# Consequences

# Positive

# Negative

# Neutral

# References
