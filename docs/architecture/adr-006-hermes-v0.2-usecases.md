# ADR 006: Hermes v0.2.0 Use-Cases

## Changelog
* 16.02.2021: Proposed.

## Context

One major problem with planning for the evolution of Hermes (the relayer
binary), is that presently there is insufficient clarity regarding its
requirements.
Some basic question here would be: who are the Hermes users, what are
their primary use-cases, and what are the primary design goals which Hermes 
should adopt towards satisfying these requirements?

In this document we do not aim to answer the above questions.
Instead, we propose a few use-cases that seem interesting from the point
of view of a general target base of users, and which will
hopefully be a subset of the requirements of future users.

Two elements that provide further context for this discussion are:

1. Some use-cases are starting to emerge ([#628][628]), which we either do not
cover altogether, or cover poorly (e.g., because of general user experience).

2. Hermes is one of three relayer binaries that are being developed roughly in
parallel. The other two are being developed in Go and Typescript, 
respectively (see the [references](#references) section).
In this context, it is plausible that Hermes will focus on performance,
robustness, and richness of features.

## Decision

The primary goal for the uses-cases we wish to cover is to prevent situations
where users could get stuck. For example this could happen because the output
of a command was not clear, or there was an error and consequently some command
finished only partially, or two relayers concurrently tried to perform some
operation(s) and interfered with each other, resulting in a chain state that is
obscure to the user.

### Patterns

We propose two basic patterns that Hermes should be able to fulfil.

1. Execute an action robustly, assuming minimal prior knowledge.
    - By "action" here we mean a command such as creating an object (connection
      or channel) on a chain or relaying packets between two chains.
    - The focus here is for the command to include retrying mechanisms 
      (perform it _robustly_) and with a simple interface.

2. Execute an action that reuses previous state that Hermes created.
    - The previous state could be a client with some specific trust options,
      for instance, and in this case Hermes would provide support for creating
      a connection that uses this specific client.
    - This pattern should also include a retrying mechanism.

### Concrete Use-Cases

- create new connection
    - with new clients
      `hermes tx connection ibc-0 ibc-1 --delay <delay>`
    - with existing clients
      `hermes tx connection ibc-0 --src-client-id <client-id> --dst-client-id <client-id> --delay <delay>`

- create new channel
    - with new connection and clients
      `hermes tx channel ibc-0 ibc-1 --src-port <port-id> --dst-port <port-id> --order <order> --version <version>`
    - with existing specified connection
      `hermes tx channel ibc-0 --src-connection <connection-id> -src-port <port-id> --dst-port <port-id> --order <order> --version <version>`

- finalize handshake for partially established connection
  `hermes tx channel ibc-0 --src-connection <connection-id>`

- finalize handshake for partially established channel
  `hermes tx channel ibc-0 --src-channel <channel-id>`

- relay packets over existing channel:
  `hermes start ibc-0 --src-channel <channel-id>`

- relay packets over a new channel that uses an existing connection:
  `hermes start ibc-0 --src-connection <connection-id> -src-port <port-id> --dst-port <port-id> --order <order> --version <version>`

- relay packets over a new channel that uses a new connection that build on an existing client:
  `hermes start ibc-0 --src-client-id <client-id> --dst-client-id <client-id> --delay <delay>`

We will write a small ADR with a few more details on this and review.


### Output


## Status
## Consequences
### Positive
### Negative
### Neutral
## References

- Relayer in Go: 
- Relayer in Typescript: 



[628]: https://github.com/informalsystems/ibc-rs/issues/628