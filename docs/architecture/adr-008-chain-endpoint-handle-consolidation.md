# ADR 008: ChainEndpoint/ChainHandle Consolidation

## Changelog
* 2022-04-19: Initial Proposal

## Context
There is a lot of common methods in the `ChainHandle` and `ChainEndpoint` traits, sometimes with minute differences between one another. This document provides a way to remove the duplication of methods for increased maintainability of the codebase, along with a few suggestions to standardize the method signatures. It also suggests a procedural macro to simplify the currently repetitive implementation of the `query_*` methods, which would be made possible given the proposed standardization of the method signatures.

## Decision

### Query methods parameters
There are currently discrepancies between how methods take their arguments. Some take a `request` object, and others take fine-grained arguments that will be used to build a `request` object in the implementation of the method. For example, `query_consensus_state()` takes arguments that will be used to build a request object, whereas `query_consensus_states()` takes a request object directly.
```rust
fn query_consensus_state(
    &self,
    client_id: ClientId,
    consensus_height: Height,
    query_height: Height,
) -> ...;

fn query_consensus_states(
    &self,
    request: QueryConsensusStatesRequest,
) -> ...;
```

All methods will be refactored to take a request object as argument.

### Query request objects
Currently, the type for the request objects is the "raw type", coming from the compiled protobuf files. For each such type, we will create a corresponding domain type, following a similar pattern as elsewhere in the codebase.

This will allow us to modify the domain type as we wish, without requiring a change in the protobuf file (and thus, requiring a change in the communication protocol). A first such change of the domain type we foresee would alter the type to specify a height in queries; however this is out of scope for this particular ADR.

### Extract common methods in a new trait `ChainBase`
All duplicated methods in `ChainEndpoint` and `ChainHandle` will be extracted in a trait called `ChainBase`. `ChainEndpoint` and `ChainHandle` will use this trait as a supertrait.

Note that there are sometimes slight differences in the return values between analogous methods. For example:
```rust
// In ChainHandle
fn query_host_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error>;

// In ChainEndpoint
fn query_host_consensus_state(&self, height: ICSHeight) -> Result<Self::ConsensusState, Error>;
```

These will end up as
```rust
fn query_host_consensus_state(&self, height: ICSHeight) -> Result<Self::ConsensusState, Error>;
```
in `ChainBase`; that is, they will return an associated type. Then, `ChainHandle` would be declared as
```rust
trait ChainHandle: ChainBase<ConsensusState=AnyConsensusState, ...> { ... }
```


### Procedural macro
We propose a procedural macro that will enhance readability of `query_*` methods. For example, in `BaseChainHandle`, the pattern looks like:
```rust
fn query_client_connections(
    &self,
    request: QueryClientConnectionsRequest,
) -> Result<Vec<ConnectionId>, Error> {
    self.send(|reply_to| ChainRequest::QueryClientConnections { request, reply_to })
}

fn query_consensus_states(
    &self,
    request: QueryConsensusStatesRequest,
) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
    self.send(|reply_to| ChainRequest::QueryConsensusStates { request, reply_to })
}

...
```

The highly repetitive implementation pattern makes it tedious to maintain, as well as see the pattern itself: a developer should check all implementations to make sure that there isn't a method which is implemented slightly differently than the others. We suggest solving this with a procedural macro.

```rust
#[unroll_template(
    [query_client_connections, QueryClientConnectionsRequest, ChainRequest::QueryClientConnections],
    [query_consensus_states, QueryClientConsensusStatesRequest, ChainRequest::QueryConsensusStates],
)]
fn _0(&self, request: _1) {
    self.send(|reply_to| _2 { request, reply_to })
}
```

In the macro expansion phase, the function definition will be duplicated once per argument provided to `unroll_template()`. Here, notice that 2 arguments are provided to `unroll_template`, 2 lists, and therefore the function definition would be duplicated twice. In each instance of the duplicated function, the markers "_0", "_1", and "_2" will be replaced by the expression at index `_i`. For example, in the first function, `_0` is replaced by `query_client_connections`, `_1` by `QueryClientConnectionsRequest`, and `_2` by `ChainRequest::QueryClientConnections`. So, the expanded code would be:

```rust
fn query_client_connections(
    &self,
    request: QueryClientConnectionsRequest,
) -> Result<Vec<ConnectionId>, Error> {
    self.send(|reply_to| ChainRequest::QueryClientConnections { request, reply_to })
}

fn query_consensus_states(
    &self,
    request: QueryConsensusStatesRequest,
) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
    self.send(|reply_to| ChainRequest::QueryConsensusStates { request, reply_to })
}
```

## Status

Proposed

## Consequences

### Positive
+ It is easier to make a change to a method in `ChainHandle` or `ChainEndpoint`
+ Increased readability of the codebase due to the use of a macro to make explicit the implementation pattern, as well as fewer lines of code to parse

### Negative
+ Developers unfamiliar with macros might find the macro version harder to understand


## References

* [Option type should be used with non-zero Height #1009](https://github.com/informalsystems/ibc-rs/issues/1009)
    + The new domain types proposed here, as well as the reduced deduplication of methods, will make fixing this issue easier
