/*!

# Concurrency Architectures

In this document, we give a high-level picture of the possible concurrency
architectures that can be be adopted for Hermes relayer v2. The relayer
framework makes it possible to implement _modular_ concurrency, and allows
the v2 relayer to offer multiple modes of operation. Aside from that, advanced
users will be able to customize the relayer framework and introduce new
concurrency architectures that are best suited for specific relaying use cases.

The relayer v2 implementations are centered around three kinds of contexts:
[relay context](crate::base::relay), [chain context](crate::base::chain),
and [transaction context](crate::base::transaction). Each context contains
the environment and dependencies that are required for operations in that
context to work. For instance, the chain context would contain parameters
for talking to a full node, and the transaction context would contain
the wallet credentials for signing transactions.

The relay context is special in that it contains _two_ chain sub-contexts.
The two chain contexts are referred to as the source context and the destination
context, corresponding to the sending of an IBC packet from the source chain
to the destination chain. Compared to relayer v1, the roles of the two chain
sub-contexts are fixed, i.e. a source chain would always remain a source chain.
This means that to perform bi-directional relaying for IBC packets for two
chains, _two_ relay contexts will needed for handling packets for each direction
separately.

In addition to the source and destination chain contexts, the relay context also
has two _dynamic_ context parameters: the _target_ chain context, and the
_counterparty_ chain context. This is to denote which chain context the relay
context is currently targeting. For example, if the relay context were to
send messages to the source chain context, then the target chain context would
be the source chain, while the counterparty chain context would be the
destination chain. This helps differentiate the different kinds of chains
the relay context is interacting with, and helps us avoid coding errors caused by
mistaking one chain with another chain.

To help visualize the concurrency architecture, a lot of details are omitted
regarding _how_ the relayer performs the operations. Instead, we focus on the steps
that the relayer will take for specific use cases.

## Single chain event source with one relay context

The first use case focuses on the relaying of multiple IBC packets
from one relay context:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-1.svg)

In the above scenario, we have a relay context with chain A being the source
chain, and chain B being the destination chain. In our scenario, we have chain A
emitting multiple source chain events that are of interest to the relay context,
which are `SendPacket` events that are targetting chain B.

When the `SendPacket` events are handled, the event handler spawns three
concurrent async tasks, all of which handle the relaying of the packets by
holding a shared reference to the relay context. The worker tasks call the
[`PacketRelayer`](crate::base::relay::traits::packet_relayer::PacketRelayer)'s
`relay_packet` method, which start the lifecycle of relaying an IBC packet.

The packet relayer may contain logics such as checking on whether the packet
has already been relayed. In our scenario, the packet relayers would construct
`RecvPacket` messages that are targeting the destination chain, chain B.
To optimize for efficiency, the packet relayers send the messages to a message
batch worker, which runs on a separate async task and receives the incoming
messages via MPSC channels.

Inside the batch worker, it collects all messages that are sent over a certain
period, such as 500ms, and attempts to consolidate them into a single batch.
In our scenario, we can assume that all chain events are emitted at the same
time, and the packet relayers manage to finish the construction of the
`RecvPacket` messages within the 500ms time frame.

With that, the batch worker attempts to consolidate the three `RecvPacket`
messages into a single batch. However, there is also a configuration for batch
size limit, and for our simplified scenario, the batch size limit is exceeded after
two `RecvPacket` messages are batched. Therefore, the batch worker sends the
three messages as two batches instead of one. The first batch would contain
the first and second `RecvPacket` messages, while the second batch contains
the third `RecvPacket` messages.

The batch worker sends the batched messages by spawning concurrent async tasks
for each batch. For each batch, the messages would go through the
[`SendIbcMessagesWithUpdateClient`](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
middleware component, which would build and attach `UpdateClient` messages to
each message batch. In this specific case, we can see that the relayer is not
being very cost-efficient, as the same `UpdateClient` messages are sent twice
for the two batches. However, the upside for this design is that the two
message batches are completely independent, and thus any failure from the first
batch would not affect the second batch. We will discuss alternative
concurrency architectures later, where there can be less redundancy on the
number of `UpdateClient` messages being sent, together with the tradeoffs made.

Moving forward, the two tasks are running concurrently to send the batched
messages to the _transaction context_. In there, the messages are processed
by a _nonce allocator_, which handles the incoming messages with a
_shared state_ and use different strategies to assign nonces for each
transaction. For example, the nonce allocator may use a _naive_ strategy,
where it _blocks_ on concurrent tasks and only allows one task to proceed at
a time. A more complex strategy would be for the nonce allocator to assign
multiple nonces and resume multiple tasks in parallel. This would allow
multiple transactions to be submitted to the chain at the same time, and have
them potentially be committed into the same block.

For the purpose of the architecture discussion, we do not go into detail about the
specific strategies of the nonce allocator use, and assume that it allows
concurrent allocation of nonces across multiple tasks. Once the nonce is
allocated, the task continues and builds the transaction with the given
nonce and messages. After that, the transactions are broadcasted to the
blockchain and the tasks would wait for the transactions to be committed.

## Success transaction result returned

We will next look at what happens after the transactions are submitted to the
blockchain. We first focus on the success case, where the transactions are
committed successfully to the blockchain:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-2.svg)

The direction of information flow for the diagram above is reversed, and flows
from right to left. First, the blockchain returns the transaction result as a
single `TXResponse` that contains the events emmitted from each message.
The events are extracted from the transaction response, and returned by
passing through the nonce allocator.

When the events are returned to the
[SendIbcMessagesWithUpdateClient](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
middleware, the component extracts the update client event from the top of the
list, and returns the remaining events. This is required, as the downstream
components require the events returned in the same order as the original
ordering of messages submitted.

After the update client event is extracted, the remaining events are split out
by the batch message component _within the same task_ as the batched messages
are sent. i.e. the result returned are _not_ processed by the batch worker task.
For the first message batch, the messages are originated from two separate
packet worker tasks. Hence, the batch component splits the first event to
be returned to the first task, and the second event to be returned to the
second task. (Note that in the actual operation, the transaction events are
grouped into a _list of list of_ events. So in our example, there are three
list of events with one event being present in each list)

For the second batched message worker task, since there were only one message
coming from the third worker task, the event is returned directly to the
third packet worker task. Once the events are returned, the packet workers
can continue with the next operations, such as relaying the ack packet messages.


## Error transaction result returned

The relayer architecture would be significantly simpler if it did not have
to account for failures and recovery. However, in practice, there are many cases
of errors that the relayer needs to handle differently, and we will go through
some of the error cases below:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-3.svg)

A common source of error during relayer operation is failures upon submitting
transactions. There are several variants of such errors. The first is that the
transaction was committed successfully to the chain, however there are errors
processing some messages, or there are transaction-level failures such as
running out of gas. In such cases, since the transaction has already been
processed, the error would need to be handled by higher-level application logic.

A second case of error is when there are errors _before_ the transaction is
processed by the blockchain. This could result from error in communication with
the full node, or error from the full node communicating with the blockchain's
P2P network. In such cases, there are not many options for the relayer other than to
_assume_ that the transaction has failed, and retry on submitting the messages
again in a different transaction.

However, since blockchains are eventually consistent systems, there is no way
for the relayer to reliably know if the transaction has truly failed or not.
There is also a possibility that the transaction has already been broadcasted
and received by other full nodes, and the transaction is eventually committed
to the blockchain, albeit more slowly than the relayer expects.

### Nonce Mismatch Errors

If the relayer incorrectly interprets a transaction as being a failure when in reality
the transaction is eventually committed successfully to the blockchain, this can
cause inconsistency in the relayer's subsequent operations. In particular,
this can cause the relayer to submit subsequent transactions with the same
nonce, thus causing the infamous account sequence (nonce) mismatch errors.
In other words, _a false failure on the relayer could result in true failure in
subsequent relayer operations_.

The first line of recovery on the relayer is handled by the nonce allocater.
It needs to interpret the returned error and choose appropriate actions to take.
In the case that the error is a nonce mismatch error, that means the nonce
allocator's cached nonce sequences have become out of sync with the blockchain.
In that case, the nonce allocator needs to fetch the up-to-date nonce from
the blockchain.

However, the nonce allocator cannot just refresh the nonce upon
encountering the first nonce error. Instead, it has to wait for all pending
transactions to return, and then refresh the nonce before allowing new
transactions to be submitted to the blockchain. The nonce allocator would also
have to be mindful of false failures returned from the transaction sender,
which may once again invalidate the nonce that it just fetched from the
blockchain. If necessary, the nonce allocator may need to make use of
exponential back off when refreshing the nonce, in order to avoid the nonce
getting perpetually out of sync.

In this first layer of error handling, the relayer needs to make a trade off
between reliability and efficiency. On one hand, the relayer can increase
reliability by waiting for a longer time to ensure that its local state reach
eventual consistency with the blockchain's state. On the other hand, the relayer
can ignore the eventual consistency and resume transaction submission quickly,
in the hope that its local state is already in sync with the blockchain's state.
To maximize the reliability, the Cosmos ecosystem may require _both_ types of
relayers to work in tandem, so that a more reliable but potentially slower
relayer can be used as a backup for the more effecient but less reliable relayer.

### Transaction Size Limit Exceeded Error

After the error is handled by the nonce allocator, it is then propagated to the
upstream components. In the message batch component, another source of error
is when the transaction sender _rejects_ the incoming messages, due to it
exceeding the maximum transaction size limit. This can potentially happen,
because it is not possible to know the actual size of the transaction until it
is encoded together with the other parameters such as nonce, signer, and
transaction memo.

Although the message batch worker does estimation on the message size when
batching messages, the estimated size may not match the actual transaction size,
depending on the way the transaction is encoded. In practice, a slight deviation
in the max transaction may not affect the relayer operations. However, some
relayer operators may have strict requirements on the maximum transaction size.
If so, the transaction sender would have to reject the transaction if the size
exceeds the max limit.

In case if the transaction size exceeds both the estimated message batch size
and the maximum transaction size limit, the error would be propagated back to
the message batch component. It the given message batch comes from more than
message sender, the batch component may retry the submission by splitting the
messages into smaller batches. Otherwise if a single message sender sends
messages that exceed the transaction size limit, the error would propagate
back to the originating message sender.

The relayer needs to have a careful strategy of when to check for the
transaction limit. On one hand, it could potentially check for the transaction
size limit when building the actual transaction. However, doing so may interfere
with the nonce allocator. This is because if the transaction sender aborts the
sending of transaction, the nonce that is being allocated to it would not be
used. This would in turns invalidate other parallel transactions that make use
of nonces that are higher than the current nonce.

An alternative strategy is to build and estimate the transaction size using
dummy fields for the nonce, signer, and fees. This may also come at the expense
of increased CPU load for encoding the transactions one extra time. Furthermore,
this requires the assumption that the size estimation using this approach is
fully accurate, as we can't fasify that assumption when the actual transaction
is built.

### Retry Relaying

If the error is not handled by the batch message component, it would then be
_cloned_ and propagated to multiple upstream message senders. This would
eventually be handled by the packet relayer, which needs to decide whether
to retry relaying the packet or not.

A potential source of error downstream is when multiple messages are batched
into a single transaction. If any message causes an on-chain error, this would
result in failure of the transaction as a whole. As a result, if any part of
the relayer submits faulty messages, it would result in failure on the other
parts of the relayer which are implemented correctly.

Fortunately, since the relaying of packets are done by separate tasks, each
packet relayer may attempt to retry the relaying independent of each others.
The first thing that a packet relayer should check is on whether it should
retry relaying the packet for the given error. For instance, if the error
is arise from transaction error caused by message batching, the packet relayer
may perform random exponential backoff to retry sending the message at a later
time. With that, the next submission of messages can hopefully not be in the
same batch as the faulty message, which would allow the message to be committed
to the chain.

The packet relayer could also perform retry if the relaying operation failed
in any stage of the pipeline. For example, there could be temporary network
failure when the update client component attempts to build the `UpdateClient`
message. There could also be errors within the packet relayer itself, such as
temporary failures when constructing the `RecvPacket` message. All these would
be handled by the top-level
[`RetryRelayer`](crate::full::relay::impls::packet_relayers::retry::RetryRelayer)
component, which would call the core packet relaying logic again if the error
is considered retryable.

## Single chain event source with one relay context (cost-optimized)

In the earlier section, we discussed about a potential room for optimization on
the construction for the building of `UpdateClient` messages, so that one
`UpdateClient` message is built for two batches of messages.

In the simplest case, a naive version of the optimization can be done by
having the batch message worker to send one batch of messages at a time,
as compared to spawning multiple tasks to send the messages. However, this
would be a trade off of minimizing the cost by increasing the latency of
messages, since the transactions cannot be submitted in parallel.

A more advanced version of the optimization can be done with the following
modification:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-4.svg)

The above optimization can be done by having a custom implementation of
[`SendIbcMessagesWithUpdateClient`](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
Using a shared state across tasks, we can make it such that the component blocks
a task if multiple tasks are trying to build `UpdateClient` messages at the
same height.

In our scenario, the `UpdateClient` message would only be built when the first
message batch, while the second message batch is blocked to wait for the
first message batch to be sent. When the `UpdateClient` message is encoded
into transactions and submitted to the mempool, the task can then send a signal
back to `SendIbcMessagesWithUpdateClient` and let it unblock the second message
task.

The optimization is slightly more complicated, because it requires the relay
context to provide shared states that can be used across the `UpdateClient`
component and the transaction sender component. It may also reduce the
reliability of the relayer, as while the second message batch is being sent, the
transaction for the first message batch may fail. If that happens, the second
message batch would also fail, due to the IBC client not being updated by
the first transaction.

It is worth noting that the first transaction would also cause the second
transaction to fail in other ways, such as nonce mismatch. However there can
be alternative ways of handling nonce, such as using multiple _nonce lanes_
or multiple signers. In such cases, the `UpdateClient` message would still
introduce additional coupling between the two transactions. Thus, it is still
important to ensure that the optimization of the `UpdateClient` messages do not
affect the improvement of reliability made by other components.

An alternative approach is to continue blocking the second message batch until
the transaction for the first message batch is committed on the chain. While
this would look similar to the batch worker itself sending messages in serial,
it still differs in that other forms of parallelism are allowed. In particular,
the message batches are only blocked when they try to build `UpdateClient`
messages at the same height. If there are new message batches arrive with
different `UpdateClient` message heights, they would be able to continue
and submit transactions to the chain in parallel.

## Single chain event source with two coupled relay contexts

The previous examples we have all work with only one relay context. Recall that
a relay context have its source and destination chains fixed. With that, a
relay context would be sending `RecvPacket` messages to the destination chain,
and `AckPacket` and `TimeoutPacket` messages to the source chain. To build a
bi-directional relayer, two relay contexts are needed to send all
three kinds of packet messages to each chain. In this case where two relay
contexts are working together to relay the IBC packets for two chain pairs,
we say that the two relay contexts are _coupled_.

When it comes to relaying efficiency, we want to ensure that the two coupled
relay contexts share the same batch worker so that messages targetting the
same chain could be in the same message batch and reuse the same `UpdateClient`
messages.

Recall that a chain context also has a _target_ mode, with the target being
either the _source target_ or the _destination target_. When two relay contexts
are coupled, the source target of the first relay context would be equivalent to
the destination target of the second relay context, and vice versa. Using that
property, we can run the message batch worker with just one of the relay
contexts with a fixed target, and still use it to process messages from the
other relay context with an _inversed_ target.

The arrangement would be as follows:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-5.svg)

In the above scenario, we have have a relay context X, with chain A being the
source chain, and chain B being the destination chain. Next, we have a relay
context Y, with chain B being the source chain, and chain B being the
destination chain. Relay context X would be responsible for sending `RecvPacket`
messages to chain B, while relay context Y would be responsible for sending
`AckPacket` and `TimeoutPacket` messages to chain B. Both relay contexts listen
to the event source from chain A, to build IBC messages that are targetted for
chain B.

To share the batch workload between relay contexts X and Y, the message batch
worker would work in a relay context Z. For the purpose of the batch worker,
it doesn't matter whether relay context Z has which chain as the source or
destination targets. Instead, it fixes the _target chain_ for relay context
Z to be chain B, and the _counterparty chain_ for relay context Z to be chain A.
This means that it is valid to use either relay context X with destination
target, or relay context Y with source target to be relay context Z.

The reason both relay contexts can be used for running the message batch worker
is because of the symmetric relation between two coupled chain contexts. As long
as the message batch worker do not make use of the source or destination chain,
it can be used for sending batched messages on behalf of both relay contexts
X and Y.

In our scenario, relay context X sends one `RecvPacket` message to the message
batch worker, and relay context Y sends one `AckPacket` message and one
`TimeoutPacket` message to the message batch worker. In the given scenario,
the message batch worker is able to combine both `RecvPacket` and `AckPacket`
messages into one batch, but have to leave the `TimeoutPacket` batch in the
second batch due to size limit. We make use of this scenario to demonstrate that
messages coming from different relay contexts can still be combined into a
single batch.

The the combined batch, both `RecvPacket` and `AckPacket` can share the same
`UpdateClient`. If we apply further optimization for `UpdateClient` such as
from the previous section, we would also be able to share the same
`UpdateClient` message with the `TimeoutPacket` message from the second batch.


## Separately batched UpdateClient sender

Traditionally, the v1 relayer would use either the latest chain height, or the
height when an IBC event is emitted to build the IBC messages such as
`RecvPacket`. While this strategy is simple, there are rooms to improve on
how the relayer should choose the height to construct the IBC messages.

For example, if the relayer needs to send a `RecvPacket` message with proof at
height 5, and then send a `AckPacket` message with proof at height 6, the
relayer would need to construct at least two `UpdateClient` messages for height
5 and 6, respectively. With the earlier concurrency architectures, the relayer
would be able to share the same `UpdateClient` messages if there are other
IBC messages with proof at heights 5 or 6. But in the case where there are only
one IBC message with proof at each of heights 5 and 6, then the relayer would
have no option but to send two separate `UpdateClient` messages.

The reason why the `UpdateClient` messages cannot be shared when the proof
heights are different has to do with how merkle proofs and light client
verification works. If we want both the `RecvPacket` and `AckPacket` messages
in the example earlier to share the `UpdateClient` message, then it is necessary
for the relayer to construct both messages at the same proof height, such as at
height 6.

To do that, the relayer needs to have an intelligent strategy to determine the
appropriate height to build IBC messages, based on the messages that it needs
to send within a given time frame. It can does so with the following
architecture:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-6.svg)

The above scenario is similar to the arrangement in the previous section, except
that we added a new "wait update client" component that would synchronize with
a new "batch UpdateClient" component. Other than that, the packet relayers are
started at different time, and each attempts to build the IBC messages with
different proof heights.

When the first packet relayer attempts to build a `RecvPacket` message, it
determines that it needs to build the message with a min proof height of 5.
However, instead of building the message straight with proof height
5, it sends a blocking query to the _batch UpdateClient_ worker to consult
which proof height is safe for it to build the IBC messages with. Similarly,
the second packet relayer wants to build an `AckPacket` message with a min
proof height 6, and the third packet relayer wants to build a `TimeoutPacket`
message with a min proof height 8, and they also send the queries to the
batch UpdateClient worker.

The batch UpdateClient worker accepts queries asynchronously and do not process
the requests immediately. Instead, it only process the queries at fixed interval,
or when there are enough number of pending queries. In our scenario, the batch
UpdateClient worker waits until it has received the queries from all three
packet workers. The worker checks that the highest proof heights from all
queries are at height 8, thus it attempts to build an `UpdateClient` message
with the update height being at least height 8.

It also happens that when the worker attempt to build the message, it also finds
the latest height of chain A to be at height 9. So instead, it builds the
`UpdateClient` message at height 9, so that the same UpdateClient could also be
potentially used for future IBC messages. The `UpdateClient` message is then
submitted as a _standalone transaction_ to chain B.

Once the `UpdateClient` message is committed to the chain, then only the
batch UpdateClient worker returns the result to all three packet workers.
In our case, all the packet workers would get height 9 being the query result,
and build the IBC messages with that being the proof height.

After building the messages, the packet relayers send the constructed IBC
messages to the batch message worker, and the messages are batched as usual.
However, when the batch message worker submits the batched messages to the
transaction context, this time it does _not_ build or include any `UpdateClient`
message to any of the message batch. This is because the batch UpdateClient
worker has already previously submitted the `UpdateClient` message as a separate
transaction, there is no need for subsequent IBC messages to include the
`UpdateClient` message if they are using the same proof heights.

### Trade offs and benefits

In this concurrency architecture, the relayer may be much slower in relaying
individual IBC packets. However, the relayer is also much more cost efficient,
as it only needs to send one `UpdateClient` message instead of three for the
above scenario. Because `UpdateClient` messages often come with high gas fees,
the reduction in the number of `UpdateClient` messages submitted could
potentially help with significant cost savings for smaller relayer operators.

As a result, this architecture allows us to build a cost-efficient relayer,
at the cost of increasing the latency of each IBC packet getting relayed.
The use of cost-efficient relaying could be helpful in use cases where the
relayer operator has low margin, and when there is little competition or
pressure for the relayers to relay IBC packets as soon as possible.

By sending the `UpdateClient` messages in separate transactions, the
architecture also gives more flexibility on how transactions can be parallelized.
If all parallel transactions are fully independent of each others, then the
failure of one transaction cannot affect the other transaction. We would also
able to make use of other parallelization approaches, such as making use of
multiple signers instead of multiple parallel nonces for submitting transactions.

On the other hand, this architecture is not necessarily useful with the
current IBC traffic load in the Cosmos ecosystem. For a cost-optimized relayer
to be useful, there needs to be on average at least one IBC packet to be relayed
between two chains at the same time. If not, the relayer could be waiting for
more than half a minute to gather enough IBC messages to batch, but still waited
for nothing when the timeout reaches. In such case, the relayer would not only
relay IBC packets more slowly, but also fail to gain any cost savings arised
from batching multiple IBC messages from nearby proof heights.

At the moment, the average IBC traffic of Cosmos chains is not high enough
for a cost-optimized relayer to be productive. There are typically gaps of
dozens of heights, before there is another IBC packet becoming available for
relaying. With such a high gap, the relayer would have to wait for minutes
before it can find two IBC packets to be batched together. As a result, the
time difference may be too high to be considered viable from a user experience
perspective.

In conclusion, it is best to revisit this architecture when there is significant
increase in IBC traffic in the future. However, considering that we
optimistically aim for a 10x to 100x increase in IBC traffic for the future,
the need for building a cost-efficient relayer may come sooner than we expect.

## Single chain event source with multiple relay contexts

In the earlier sections, we have been covering the scenarios of relaying between
one relay context, or two coupled relay contexts. However both cases only
involved the relaying of IBC packets between two chains. In a multichain world,
the relayer would need to relay packets from many chains, and with that there
are additional room for improving the efficiency of relaying IBC packets from
multiple chains.

Consider a simple scenario, where the relayer needs to send one `RecvPacket`
message from chain A to chain B, and one `RecvPacket` from _chain C_ to chain B.
In this case, the relayer would need to also build an `UpdateClient` message for
chain A's client on chain B, as well as an `UpdateClient` message for chain C's
client on chain B. With that, there are a total of four IBC messages to be sent
to chain B.

If the relayer tries to relay all four IBC messages at roughly the same time,
there is an opportunity to batch all messages into a single transaction.
However in relayer v1, such optimization is not done, as the relayer only batch
IBC messages between two chains as specified in the `RelayPath` construct.

In the v2 relayer, we can batch IBC messages from multiple chains by adding
an additional layer of message batch worker as follows:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-7.svg)

In the above scenario, we have a relay context X, with the source chain being
chain A, and the destination chain being chain B. We also have a relay context Y,
with the source chain being chain B, and the destination chain being _chain C_.
Relay context X would be using the IBC event source from chain A as the
source chain event source, and relay `RecvPacket` messages from there. On the
other hand, relay context Y would be using the IBC event source from chain
C as the destination chain event source, and relay `AckPacket` and
`TimeoutPacket` messages from there.

In relay context X, the packet relayers attempt to send two `RecvPacket`
messages from different concurrent tasks. The two messages would first be
handled by the relay-level message batch worker in the same way as previous
examples, and the two messages are combined into the same batch. The batch
worker then spawns a task for sending the batched messages. Inside the task,
the `UpdateClient` message is built and prepended to the message batch.
Following that, instead of sending the messages to the transaction context,
the task sends the message batch to another message batch worker, which works
at the chain-level.

In relay context Y, the packet relayers attempt to send one `TimeoutPacket`
message. The message pass through the relay-level message batch worker without
additional batching, and then builds the `UpdateClient` message to be sent
together with the `TimeoutPacket` message. The two messages are then sent to
the chain-level message batch worker. Notice that the `UpdateClient` message
here is from chain C, while the `UpdateClient` message from relay context X is
from chain A.

The chain-level message batch worker receives the batched messages from both
relay context X and relay context Y. It then combines all five messages into
a single batch and sends it to the transaction context. The five messages are
then submitted to the blockchain as a single transaction.

In this architecture, the relayer can potentially achieve higher cost efficiency
by combining messages from multiple chain into a single batch. As today's IBC
traffic is relatively low, it is less frequent to have the relayer sending
multiple IBC messages from one chain to another chain. But as the relayer relays
between more chains, it becomes increasingly likely that at any one time,
there are IBC messages from two or more chain that needs to be sent to a common
chain. As a result, this design may help reduce the relaying cost, if the
fee for sending one transaction with the combined messages is lower than sending
them as two or more transaction.

This architecture is likely also implemented by the Go relayer, as we have seen
messages from multiple chains being batched in this way when inspecting the
transaction logs from non-Hermes relayers.

The downside of this architecture is that there may be a slight increase in
latency for the messages to be relayed. This is because there are now two
batch message workers that are running separately, and each of them needs to
collect incoming messages across a timeframe in order to combine them into
one batch. Furthermore, there is a higher chance for faulty messages from one
chain to affect the messages from other chains, due to them being batched
into the same transaction.

On the other hand, this architecture may also help in improving the reliability
of the relayer from a different aspect. If more messages can be combined into
a single transaction, then there is less need for the relayer to submit
multiple parallel transactions at the same time. If the relayer is able to
submit only one transaction to each chain during most of the time, then there
is less likely for the relayer to encounter concurrency errors caused by
the nonce mismatch error arise from the use of multiple nonces.


## Batching packets from both ordered channels and unordered channels

In the previous sections, we discussed highly concurrent architectures that
are designed to handle packets from unordered channels. However in IBC, ordered
channels impose additional requirements that packets from that channel must be
delivered in the same order. This introduce additional complexity when
in our concurrent system, as tasks would need some ways to synchronize and
wait for each others to complete.

To understand why the ordering of packets require additional synchronization,
consider the original design we have for running multiple packet workers in
parallel, and batching the outgoing messages with a message batch worker. A
naive attempt to enforce the packet ordering would be to spawn a packet worker
for a packet with lower sequence before spawning a packet worker for another
packet with the next sequence. However since each packet worker would perform
multiple operations in parallel before they can produce the message to be sent,
there is no guarantee that the first packet worker that is spawned will send its
messages before the second packet worker.

Furthermore, even if messages are sent in the same order, they would not ended
up being sent as transactions in the same order. This is because between the
time a message is sent and a transaction is sent, there are various other
operations involved such as the message batching operations, building the
`UpdateClient` messages, estimating the transaction fees, and encoding the
transaction.

A naive workaround for this is that we could remove the concurrency aspects and
send the ordered packets in serial. However this would mean that only one
ordered packet can be relayed in one transaction at a time. A better alternative
is to keep the existing concurrency architecture, and introduce additional
layers for relaying ordered packets:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next/docs/architecture/assets/concurrency-architecture-8.svg)


The above scenario describes a case where the relayer is using the same relay
context to relay multiple channels. Between chain A and chain B, there is one
ordered channel `channel-1` and one unordered channel `channel-2`. The source
chain event listener listens to the events from the source chain, chain A, and
found three packets to relay:

1. `channel-1` with sequence 8.
2. `channel-1` with sequence 9.
3. `channel-2` with sequence 16.

The first two packets are from the ordered channel `channel-1` with sequences 8
and 9, and they must be sent in the same order. The third packet is from the
unordered channel `channel-2`, and it can be sent without need for
synchronization. The event listener spawns three packet worker tasks for each
packet, but with the worker tasks for the ordered packets behaving differently.

### Ordered Packet Worker

In the packet worker task for the first packet, it tries to relay the packet
with sequence 8 from `channel-1`. But since `channel-1` is an ordered channel,
it performs a check on whether the packet with sequence 7 from the same channel
has been relayed previously, or is currently being relayed by another packet
worker. It finds that neither case is true, and thus it spawns an extra packet
worker task to relay the packet with sequence 7. The packet then resumes
immediately to relay the packet with sequence 8.

Inside the extra packet worker, it also performs the same check for ordered
packets, and found that the packet with sequence 6 has already been relayed,
so it proceeds to relay the packet with sequence 7.

In the packet worker task for the second packet, it tries to relay the packet
with sequence 9 from `channel-1`. It performs the ordered packet checks, and
found that the other packet worker has already been relaying the packet with
sequence 8. So it continues its operation to relay sequence 9.

In the packet worker task for the third packet, it tries to relay the packet
with sequence 16 from the unordered channel `channel-2`. So it proceeds straight
to the relaying operation, and send the constructed `RecvPacket` message to
the message batch worker in the same way as described in previous sections.

### Packet Sequencer

For the packet workers relaying the ordered packets, instead of sending the
constructed `RecvPacket` messages directly to the message batch worker, they
would send the messages to a _packet sequencer_. The packet sequencer is a
worker task that runs separately from the message batch worker. It is
responsible for enforcing the ordering of sent packets before sending them to
the message batch worker. The packet sequencer task is spawned
_per ordered channel_. So if there are packets from multiple ordered channels,
they will be sent to different packet sequencer tasks.

In our scenario, the `RecvPacket` message for sequence 8 is the first one to be
sent to the packet sequencer. The packet sequencer checks on whether the
`RecvPacket` message for sequence 7 has already been sent before, and found that
it has not. So the packet sequencer stores the `RecvPacket` message in the queue,
and wait for the message with sequence 7 to arrive.

While our packet sequencer is waiting for sequence 7, the `RecvPacket` message
with sequence 9 has also been sent. The packet sequencer once again confirms
that the `RecvPacket` with sequence 7 has not been sent by other tasks or by
external relayers, so it continues to wait.

Finally, the `RecvPacket` for sequence 7 is received by the packet worker. The
packet sequencer also confirms that the packet for sequence 6 has already
previously been relayed. So with that, it attempts to send all three `RecvPacket`
messages for sequence 7, 8, 9. It first checks that the combined message size
have not exceeded the batch size limit, and then sends the three messages
in a single batch to the message batch worker.

In case if the packet sequencer did not receive the `RecvPacket` message with
sequence 7 within a time limit, it would instead return an error to signal to
the packet workers that the ordered packets for earlier sequence was not
received within the time limit. In reaction to that, the ordered packet workers
may attempt to spawn new packet workers for the earlier sequence, in case the
previous packet workers failed for some reason.

### Batching messages from multiple channels

The message batch worker runs in the same way as described in the earlier
sections. In this scenario, it first receives the `RecvPacket` message from
the unordered channel `channel-2`. It waits for a while, and then receives the 3
messages from the packet sequencer. It then attempt to combine all 4 messages in
a single batch. In this scenario, the total batch size are within the limit,
and the message batch worker proceeds to send the 4 messages together.

The 4 messages are then go through the `UpdateClient` message sender, which
scans through the messages and prepend `UpdateClient` messages to the front
of the message list. Finally, all messages are sent to the transaction sender,
which sends the messages all in a single transaction.

The above scenario demonstrates that messages from ordered channels can be
processed in parallel by adding a packet sequence component to process
the messages between the ordered packet workers and the message batch worker.
The scenario also shows that ordered packet messages can be processed in
parallel with unordered packet messages, and then be batched together in the
same transaction.

This concurrency architecture helps ensure that the relayer pays for the cost of
relaying ordered packets only when necessary. If there is no ordered channels,
the additional logic for relaying ordered packets wouldn't be triggered. If
there are multiple ordered channels, they can be relayed in parallel, have
the ordering enforced by multiple packet sequences, and then be batched into
the same transaction.



*/
