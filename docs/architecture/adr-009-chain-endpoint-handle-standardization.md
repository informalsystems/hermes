# ADR 009: ChainEndpoint and ChainHandle methods standardization

## Status

Accepted - The PR has been merged in [#2108](https://github.com/informalsystems/hermes/pull/2108)

## Changelog
* 2022-04-19: Initial Proposal

## Context
There is a lot of common methods in the `ChainHandle` and `ChainEndpoint` traits, sometimes with minute differences between one another. This document provides a way to remove the duplication of methods for increased maintainability of the codebase, along with a few suggestions to standardize the method signatures. 

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


## Consequences

### Positive
+ The protobuf types are not exposed directly, which allows `hermes` to work with future non-tendermint chains
+ Increased readability of the codebase; similar methods have a similar format

### Negative


## References

* [Option type should be used with non-zero Height #1009](https://github.com/informalsystems/hermes/issues/1009)
    + The new domain types proposed here, as well as the reduced deduplication of methods, will make fixing this issue easier
