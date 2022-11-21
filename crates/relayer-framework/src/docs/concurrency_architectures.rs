/*!

# Concurrency Architectures

In this document, we give a high-level picture of the possible concurrency
architectures that can be be adopted for Hermes relayer v2. The relayer
framework makes it possible to implement _modular_ concurrency, and allows
the v2 relayer to offer multiple modes of operation. Aside from that, advanced
users will be able to customize the relayer framework and introduce new
concurrency architectures that are best suited for specific relaying use cases.

The relayer v2 implementations are centered around three kinds of contexts:
relay context, chain context, and transaction context. Each context contains
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
have two _dynamic_ context parameters: the _target_ chain context, and the
_counterparty_ chain context. This is to denote which chain context the relay
context is currently targetting on. For example, if the relay context were to
send messages to the source chain context, then the target chain context would
be the source chain, while the counterparty chain context would be the
destination chain. This helps differentiates the different kinds of chain
the relay context is interacting with, and avoid the coding errors caused by
mistaking one chain with another chain.

To help visualize the concurrency architecture, a lot of details are omitted for
_how_ the relayer performs the operations. Instead, we would focus on the steps
that the relayer would take for specific use cases.

## Single chain event source with one relay context

The first use case would be focused on the relaying of multiple IBC packets
from one relay context:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-1.svg)

In the above scenario, we have a relay context with chain A being the source
chain, and chain B being the destination chain. In our scenario, we have chain A
emitting multiple source chain events that are of interest of the relay context,
which are `SendPacket` events that are targetting chain B.

When the `SendPacket` events are handled, the event handler spawns three
concurrent async tasks, all of which handles the relaying of the packets by
holding a shared reference to the relay context. The worker tasks would
call the `PacketRelayer`'s `relay_packet` method, which would start the
lifecycle of relaying an IBC packet.

The packet relayer may contain logics such as checking on whether the packet
has already been relayed. in our scenario, the packet relayers would construct
`RecvPacket` messages that are targetting the destination chain, chain B.
To optimize for efficiency, the packet relayers send the messages to a message
batch worker, which runs on a separate async task and receive the incoming
messages via MPSC channels.

Inside the batch worker, it collects all messages that are sent over a certain
period, such as 500ms, and attempt to consolidate them into a single batch.
In our scenario, we can assume that all chain events are emitted at the same
time, and the packet relayers manage to finish the construction of the
`RecvPacket` messages within the 500ms time frame.

With that, the batch worker attempts to consolidate the three `RecvPacket`
messages into a single batch. However, there is also a configuration for batch
size limit, and for our simplified scenario, the batch size limit exceeds after
two `RecvPacket` messages are batched. Therefore, the batch worker sends the
three messages as two batches instead of one. The first batch would contain
the first and second `RecvPacket` messages, while the second batch contains
the third `RecvPacket` messages.

The batch worker sends the batched messages by spawning concurrent async tasks
for each batch. For each of the batch, the messages would go through the
[SendIbcMessagesWithUpdateClient](crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient)
middleware component, which would build and attach `UpdateClient` messages to
each message batch. In this specific case, we can see that the relayer is not
being very cost-efficient, as the same `UpdateClient` messages are sent twice
for the two batches. However, the upside for this design is that the two
message batches are completely independent, and thus any failure from the first
batch would not affect the second batch. We will discuss about alternative
concurrency architectures later, where there can be less redundancy on the
number of `UpdateClient` messages being sent, together with the tradeoffs made.

Moving forward, the two tasks are running concurrently to send the batched
messages to the _transaction context_. In there, the messages are processed
by a _nonce allocator_, which handles the incoming messages with a
_shared state_ and use different strategies to assign nonces for each
transaction. For example, the nonce allocator may use a _naive_ strategy,
where it _blocks_ on concurrent tasks and only allow one task to proceed at
a time. A more complex strategy would be for the nonce allocator to assign
multiple nonces and resume multiple tasks in parallel. This would allow
multiple transactions to be submitted to the chain at the same time, and have
them potentially be committed into the same block.

For the purpose of the architecture discussion, we do not go into detail the
specific strategies the nonce allocator use, and assume that it allows
concurrent allocation of nonces across multiple tasks. Once the nonce is
allocated, the task continues and builds the transaction with the given
nonce and messages. After that, the transactions are broadcasted to the
blockchain and the tasks would wait for the transactions to be committed.

## Success transaction result returned

We will next look at what happens after the transactions are submitted to the
blockchain. We first focus on the success case, where the transactions are
committed successfully to the blockchain:

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-2.svg)

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

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-3.svg)

## Single chain event source with one relay context (cost-optimized)

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-4.svg)

## Single chain event source with two coupled relay contexts

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-5.svg)


## Separately batched UpdateClient sender


![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-6.svg)

## Single chain event source with multiple relay contexts

![Concurrency Architecture](https://raw.githubusercontent.com/informalsystems/hermes/soares/relayer-next-adr/docs/architecture/assets/concurrency-architecture-7.svg)

*/
