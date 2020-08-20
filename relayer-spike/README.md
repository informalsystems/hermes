Relyaer Spike
=============

The goal is to outline the relayer logic as an object graph that can
abstract over concurrency and IO.

## Objects

LocalClient
    * Light clients embeded in the relayer

RemoteClient
    * Can be updated
        * Updating means producing update dragrams

Chain
    * Can be queried
    * Materialize (cache) state from the chain
    * produce subcriptions (event streams)
        * Can produce route events to different subscriptions
    * Have a RemoteClient 
    * can be sent Packets

Subscriptions (event Monitor)
    * Iterable stream of events
    * Construct datagrams 

Connections
    * ICS3
    * Required two chains
    * require a specific set of events
    * Are stateful
    * Materialized view on state of two chains
    * Performs handshake algorithm

Channels
    * Requires a connection
    * Materialized view of on-chain state
    * can timeout?
        * Does it require upkeep?

Packets
    * Are the product of events and queries
    * Batch multiple datagrams together

## Testing Regimen
* RemoteClient
    * With valid full node
    * With invalid full node (verification fails)
* Connection setup
    Connection handshake as the function of two chain states
    * With out of date client
    * Channel setup
* Channel Setup
    * Function of chain states
* Packet construction
    * As the function of a two chain states

## Stage 1: Synchronous abstractions:
    * Chain, Subscription abstraction
    * Sketch dependency graph
    * Connection construction
    * Channel construction

## Stage 2: Runtime
    * produce relayer construction with handler facades for concurrent runtimes


We need to decide:
* Should Client Update be bundled with packet submission?
* Q: Are packet submissions synchronous or are they handled by an internal
  chain runtime?
* A: Let's just do it synchronously and inefficient for now

* What are the failure cases for Relay
    * Submission fails
    * proof verification fails
    * light client fails
    * `client_update` fails
* All these will produce context specific errors that will be mapped to
  relay errors which can be processed by a relay manager

## TODO: 
* Outline CLI requirements

Here is the configuraiton that we need to establish a link
```
{
  "src": {
    "chain-id": "ibc0",
    "client-id": "ibconeclient",
    "connection-id": "ibconeconnection",
    "channel-id": "ibconexfer",
    "port-id": "transfer",
    "order": "ordered"
  },
  "dst": {
    "chain-id": "ibc1",
    "client-id": "ibczeroclient",
    "connection-id": "ibczeroconnection",
    "channel-id": "ibczeroxfer",
    "port-id": "transfer",
    "order": "ordered"
  },
  "strategy": {
    "type": "naive" // what does this mean?
  }
}
```

    * Outline Path construction
        * Construct a Channel and Connection
    * Understand the dependency graph between the components

Imagine a polling subscription, pulling data from the full node
It may get a packet from
    * A connection
    * A Channel establishment
    * A Packet being forwarded
