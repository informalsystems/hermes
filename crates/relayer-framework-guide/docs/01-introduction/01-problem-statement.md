# Problem Statement

The IBC relayer framework is designed to solve multiple problems simultaneously:

- The need for multiple relaying strategies, including cross-cutting concerns for:
  - Message batching
  - Error retry
  - Update client mechanics
  - Prioritized mempools
  - Multi-wallet batching
  - Async pipeline

- Distinguish values coming from different chains.

- Handling differences in protobuf definitions and behavior that arise from different Cosmos
  chain implementations such as:
  - Tendermint
  - Cosmos SDK
  - ibc-go

- Handling relaying from non-Cosmos SDK chains, such as:
  - Nomic
  - Penumbra

- Handling relaying from non-Cosmos chains, such as:
  - Substrate

## Message Batching

A naive relayer can easily perform IBC relaying for a single packet by building
the relevant proofs on one chain and submit the messages to the counterparty
chain. However such relaying is slow and wasteful of fees, as the relayer
can only relay one packet in each transaction.

As a result, batching mechanics are introduced to batch multiple messages for
one chain into a single transaction. This significantly complicates the relayer
design, and is the main source of complexity in the current relayer.

Ideally, the core relayer logic should be kept simple and implemented as close
to a naive relayer. Additional logics like message batching are cross-cutting
concerns that should be implemented in a way that _augments_ the core logic,
not to obscure it.

## Error Retry

In a distributed system, the relaying operations may fail due to external
factors, such as a network disconnection and full node going down. Therefore
the relayer needs to implement retry logic to resubmit a relay message to
a chain when it fails.

However when working the batching mechanics, the retry logic becomes
significantly more complicated. Since batched messages in a transaction would
all fail when one message fails, it is unclear what caused the errors,
and how the retry should be done.

The current relayer rely on ad-hoc retry mechanisms at various levels of
code. There is no clear understanding of how the errors propagate, and
we are playing whack-a-mole to hammer down errors when relaying fail.

Ideally, the error retry should be done at the level of relaying for a single
packet. This is so that the retry operations can be done independently of each
packet.

## Update Client Mechanics

The relayer needs multiple strategies of when to submit `UpdateClient` messages
inside the transactions it submitted to a chain. For IBC messages like
`RecvPacket` to be accepted by the chain, an `UpdateClient` message with the
corresponding height must already be processed either before the current
transaction, or in the messages before the current message in the current
transaction.

When redundant `UpdateClient` messages of the same height are submitted,
the subsequent messages are ignored, but the relayer still have to pay for the
fee. Therefore to be cost effective, the relayer should avoid sending
multiple `UpdateClient` messages whenever it is possible.

When combined with the message batching mechanics, the update client subsystem
has to decide whether to prepend an `UpdateClient` message to the current
batched transaction.

When combined with the error retry mechanics, the update client subsystem has
to determine whether it is safe to skip prepending the `UpdateClient` message
to the current batch, if the `UpdateClient` message is prepended to the
previous batch but failed.

The current relayer architecture is not very flexible at using different
strategies to update clients. Therefore it can fail in unexpected ways
when transactions with `UpdateClient` fail. The relayer is also inefficient
due to messages forming dependencies to the transaction with `UpdateClient`,
making it difficult to submit multiple transactions in parallel.

## Prioritized Mempools

The upcoming changes for prioritized mempools in Tendermint breaks the current
batching mechanics of submitting multiple transactions in parallel. Because a
chain can now process the transactions in any order, it is possible to break
the original ordering and have a transaction without `UpdateClient` to be
processed before the transaction containing `UpdateClient`.

To workaround the limitation, we have to come up with new strategies on how to
batch transactions with `UpdateClient` messages. A naive approach would be
to prepend the `UpdateClient` message to _all_ transactions, which can be
wasteful in cost.

A better strategy would be to focus on _throughput_ rather than latency.
That can be done by submitting `UpdateClient` transactions independently,
and only batch and submit IBC messages in parallel when the `UpdateClient`
transaction is committed.

The problem of choosing a suitable strategy is that the current relayer
architecture is tightly coupled with a specific strategy. Therefore it is
very difficult to change the relaying strategy, or experiment on better
strategies.

Ideally, the core logic of the relayer should be independent of the strategies
of how the messages are batched and how the `UpdateClient` messages are
prepended.

## Multi-Wallet Batching

The current relayer architecture is hardcoded with one global wallet per chain,
and it is difficult to use a different wallet for sending messages without
spawning an entirely separate `ChainHandle` instance together with the
surrounding wiring. This makes it challenging for the relayer to adopt more
efficient message batching strategies that make use of multiple wallets.

Cosmos chains are configured with soft limits of how large a single transaction
can be. As a result, the relayer cannot simply batch unbounded number of
messages in a single transaction. This creates a problem when the relayer
needs to relay many IBC packets at the same time. The transaction bottleneck
means that messages have to be queued and be sent one after another.

A further complication of the message queue is that each transaction is
assigned an account sequence that must be greater than the sequence used in the
previous transaction. If multiple transactions are submitted to the mempool,
a transaction with lower sequence number will get rejected if it gets processed
after another transaction with a higher sequence number. This issue is further
aggravated with the introduction of prioritized mempools.

The safest way to workaround this problem is to ensure that only one
transaction is being processed by the mempool at any time. However this will
also introduce additional latency, as new transaction can only be submitted
after the previous transaction is committed to a block, meaning that the
next block has to be skipped and the next transaction can be committed
earliest in the block after.

A better strategy would be to also use multiple wallets at the same time,
so that each wallet can submit different transactions in parallel without
blocking each others.

To do this, the relayer architecture needs to allow customization of wallets
used for relaying, and lazily instantiate the signer fields and signatures
depending on the availability of parallel wallets.

## Async Pipeline

The current relayer architecture was implemented before async Rust become
stabilized. As a result it uses threads for concurrency, which limits the
number of concurrent processes that can run.

Since spawning new threads are expensive, the current relayer spawns a worker
thread for each relay path as identified by source and destination
channels/chains. When combined with the batching and retry operations, this
means that the packet worker has to do ad hoc multiplexing strategies to
process multiple IBC packets in parallel within a single thread. This results
in non-linear control flow and makes the relaying code difficult to understand.

With async Rust available now, a better approach is to redesign the packet
worker such that they can be run in multiple async tasks. For instance, the
relaying of each packet can be done in separate async tasks, with each having
their own retry logic. The message batching operation can be done in separate
async tasks, and communicate with the individual packet relaying tasks through
message passing.

## Multi-Versioned Protobuf Definitions

The relayer currently uses [`prost_build`](https://docs.rs/prost-build/) to
generate Rust structs from the protobuf definitions provided by the Go projects
`tendermint`, `cosmos-sdk`, and `ibc-go`.

When running a Cosmos chain, it is trivial to use a single set of protobuf
definition, as the chain is acting as the provider for the protobuf-based
services. However as a client, the relayer acts as a client to interact with
many chains, and has to support relaying between different chains, even if
they use incompatible versions of protobuf definitions.

The use of a single set of protobuf definitions cause issues when supporting
chains that do not use the same protobuf definitions. To support newer chains,
the relayer must update the protobuf definitions to support the new features.
But if the new protobuf definitions contain breaking changes, it would break
relayer support for chains that are still using the older definitions.

A better strategy is to generate _multiple_ protobuf definitions for each
major versions, and have them co-exist within the relayer. However a major
challenge with this approach is that the different protobuf definitions
are considered different types by Rust, even if they are structurally
equivalent.

For example, if a Rust code is written to work with the `Height` struct
from one version of the protobuf definitions, Rust will reject the code
if we pass it a value with the `Height` type from another version of the
protobuf definitions, even if between the two versions, the fields in
`Height` are exactly the same.

In this case, it is also not possible to use feature flags to switch between
different protobuf versions, because the relayer may need _both_ versions
during runtime.

A more appropriate solution is to treat all protobuf types as _abstract_,
and write _generic_ code that work with any protobuf type that satisfy
higher level constraints.

For example, a Rust code can be written to be generic over any `Height`
type, provided that the type implements `Eq`, `Ord`, and `Clone`. With this,
the code can be used with different sets of protobuf definitions, even if
there are other protobuf structs that are incompatible but are unused by
the given code.

## Multi-Versioned RPC APIs

Cosmos chain implementations do not only provide protobuf definitions, but
also offer RPC and GRPC services. However similar to the protobuf definitions,
the RPC APIs can change and break in subtle ways.

A common form of breakage is when the APIs require additional input fields or
return additional/less fields in the response. Another form of breakage is on
subtle changes in the JSON scheme and causing mismatch in field names.

With the current relayer design, there is often no way to solve it on the
relayer side, other than reporting the errors and hope that the upstream
APIs revert the changes.

A more appropriate design is to allow the API clients to be customized and
overridden depending on the chains. So if a particular API has breaking
changes, there can be two version of API clients to choose from.

## Support for Non-SDK Chains

Cosmos chains that are based on Cosmos SDK offer a fairly standard set of
GRPC APIs by reusing what has already been implemented in Cosmos SDK.
But with the decoupling offered by Tendermint and ABCI, there are also
Cosmos chains that are not implemented using Go and Cosmos SDK.

These non-SDK chains may not necessary offer the same GRPC APIs or protobuf
definitions. So the relayer may break in unexpected ways when relaying from
non-SDK chains.

While non-SDK chains may be incentivized to preserve the same behavior as
SDK chains, this puts unnecessary burden to the chain developers. Furthermore,
not all chains are compelled to use Hermes as the IBC relayer, and Hermes
may lose its competitive advantage if there are relayers that can work better
with non-SDK chains.

For the long term health of the Cosmos ecosystem, it is also worthwhile to
encourage alternative implementations of Cosmos SDK and IBC in languages
other than Go. For this, the Hermes relayer should be made customizable so that
non-SDK chain developers can more easily customize the relayer to work with
their custom chains.

## Support for Non-Cosmos Chains

The biggest challenge with the current relayer architecture is to extend it
to work with non-Cosmos chains like Substrate. In particular, the relayer
data structures are tightly coupled with Cosmos-related protobuf definitions
and RPC APIs. But non-Cosmos chains are not obligated to use protobuf or
GRPC.

The relayer code is also tightly coupled with concrete data structures, making
it difficult to extend the data structures to work differently for non-Cosmos
chains. This problem is seen most notably in the definition of sum types like
`AnyClientState`, in attempt to have global types but still support variants
of the concrete data structures.

All these means that the core relayer code and global types have to go through
significant changes to support a new non-Cosmos chain. Due to conflicts and
additional dependencies, this often result in forks of the relayer just so
that changes can be made without interfering with the core relayer development.

The primary goal for us with a new relayer design is to have a minimal set of
assumptions on how an IBC-like relaying should work, and expose the relayer
core logic as a libary so that non-Cosmos chains can use the library to develop
custom relayers without having to fork the entire relayer.
