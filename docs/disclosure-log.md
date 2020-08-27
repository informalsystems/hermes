# Disclosure Log for IBC Protocols

This document is a record of all the bugs or issues we uncovered while specifying & formally verifying the IBC protocols.


### 1. ICS3 liveness problem due to ICS018 relayer algorithm

The algorithm for relaying connection handshake datagrams of type `ConnOpenTry`does not handle the situation when both chains are in state `INIT`.
The current relayer algorithm in [ICS018](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms) specifies that the `ConnOpenTry` datagram should be relayed only if one of the chains is in state `INIT` and the other chain is uninitialized (see the snippet below); this is not enough for guaranteeing liveness of the connection handshake protocol (ICS04).

```
    if (localEnd.state === INIT && remoteEnd === null)
```

The correct code should include both the cases when a single chain is in state `INIT`, as well as the case when both chains are in state `INIT`, as specified here: [Relayer.tla](https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Relayer.tla#L174)
This fix only concerns the relayer algorithm ICS018.

##### Channel handshake (ICS4) liveness problem

The same issue (and fix) seems to exist for the channel handshake datagrams.


### 2. ICS3 liveness problem due to `UpdateClient` semantics

This problem is not specific to the connection handshake protocol (ICS3) itself, but is a bug in the way the relayers use the `UpdateClient` action.
We classify this under ICS3, however, since this is the context where we discovered the problem.
The TLA+ spec we have for depicting this liveness problem is for the ICS3 protocol.

##### Problem statement

Related issues: [#71](https://github.com/informalsystems/ibc-rs/issues/71) and [#61](https://github.com/informalsystems/ibc-rs/issues/61).
The problem is more thorougly described in #61, but for completeness sake we restated it here in a compact form.

The liveness property that a correct relayer should provide is eventual delivery.
Assuming some source chain `A`, destination chain `B`, and an IBC item `X` (e.g., connection, channel, or packet) on chain `A`, we can define this property as follows:

> For any IBC item `X` on chain `A` destined for chain `B`, eventually, a correct relayer will submit item `X` to chain `B`.

This is difficult to guarantee in practice, however.
Intuitively, the difficulty arises because of a combination of two factors:

1. __Proof requirement:__ For chain `B` to accept item `X`, it must verify the authenticity of this item; this is done via the light client that chain `B` maintains.
Given an item `X` and a commitment proof for `X` constructed at height `h-1`, the light client requires the consensus state at height `h` that includes that commitment root required for verification.

2. __Concurrency:__ Different relayers may update the same light client.
Suppose a relayer `r1` wants to submit a consensus state at height `h`.
In the meantime, however, another relayer `r2` may update this same light client to height `h'`.
Assume `h'` is bigger than `h`.
If the light client disallows updates with heights smaller than the current height `h'` then `r1`'s update fails .
Consequently, the relayer will be unable to submit consensus state at height `h`.

To ensure eventual delivery, relayer `r1` would need to retry submitting item `X`, that is: resubmit the consensus state at a larger height (e.g., at `h'`) followed by the message that includes the proof for `X` (e.g., at `h'-1`).
This retry mechanism was adoped as a solution for the [current relayer implementation](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-002-ibc-relayer.md#ibc-client-consensus-state-vs-relayer-light-client-states-vs-chain-states).
Note that it is also possible for relayer `r2` to have submitted the same item `X` successfully; in this case, the liveness problem does not actually surface.


##### TLA+ trace

> Note that the TLA+ spec below may change in time. Here we refer to the spec as [existing at this commit](https://github.com/informalsystems/ibc-rs/tree/788c36be9e14725c542bd586b4fe4593edb3ca80/docs/spec/connection-handshake/L2-tla) (unchanged up to [release 0.0.2](https://github.com/informalsystems/ibc-rs/releases/tag/v0.0.2)).  

To obtain an execution in TLA+ that depicts the above liveness problem, it is sufficient to enable the `Concurrency` flag in the L2 default TLA+ spec for ICS3.
This spec is located in [spec/connection-handshake/L2-tla/](./spec/connection-handshake/L2-tla/).
In this spec we make a few simplifications compared to the real system, most importantly: to verify an item at height `h`, a light client can use the consensus state at the same height `h` (no need for smaller height `h-1`).
Below we summarize the parameters as well as the sequence of actions that lead to the liveness problem.

###### Parameters:

- `MaxBufLen <- 2`
- `MaxHeight <- 8`
- `Concurrency <- TRUE`
- Behavior spec: Temporal formula `Spec`
- Check for `Deadlock`, Invariants `TypeInvariant` and `ConsistencyProperty`, as well as Property `Termination`

###### Trace:

Both chains `A` and `B` start at height `1`, and the light client on each chain has consensus state for height `1`.

1. The environment submits a `ICS3MsgInit` message to chain `A`.

2. Chain `A` processes the `ICS3MsgInit`, advances to height `2`, and prepares a `ICS3MsgTry` message destined for chain `B`.
The proof in this message is for height `2`.

3. The environment triggers the `AdvanceChainHeight` action of chain `B`, so this chain transitions from height `1` to height `2`.

4. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `2` to height `3`.

5. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `3` to height `4`.

6. __Concurrency:__ The environment triggers the `UpdateClient` action on chain `B`: the light client on this chain is updated with height `4` (that is, the latest height of chain `A`), and chain `B` also transitions from height `2` to height `3`.

7. The environment passes (i.e., relays) the `ICS3MsgTry` message to chain `B`.
Recall that this message has proofs for height `2`; consenquently, the environment also attempts to trigger `UpdateClient` action on chain `B` for consensus state at height `2`.
This action does not enable because the light client on `B` has a more recent consensus state for height `4`.

8. Chain `B` attempts to process the `ICS3MsgTry` but is unable to verify its authenticity, since the light client on this chain does not have the required consensus state at height `2`.
Chain `B` drops this message.

From this point on, the model stutters, i.e., is unable to progress further in the connection handshake protocol.


### 2. ICS3 problems due to version negotiation

The original issue triggering this discussion is here: [cosmos/ics/#459](https://github.com/cosmos/ics/issues/459).
This section is still WIP.

##### Case (.). Liveness issue caused by overwriting the version
Setup:
- Model parameters:
```
Concurrency <- FALSE
MaxBufLen <- 2
MaxHeight <- 7
MaxVersionNr <- 2
VersionPickMode <- "onTryNonDet"
```
- Check for _Deadlock_ and property _Termination_.

Outcome:
- Model checking halts with exception "Temporal properties were violated."
- The issue is that the version in the two chains diverges


##### Case (a). Liveness issue caused by empty version intersection

Model checking details in TLA+:
- Model parameters:
```
Concurrency <- FALSE
MaxBufLen <- 2
MaxHeight <- 7
MaxVersionNr <- 2
VersionPickMode <- "overwrite"
```
- Check for _Deadlock_ and property _Termination_.
- Model checking halts with exception "Temporal properties were violated."

Trace: the two chains start off with different versions ("1" for A, and "2" for B),
consequently the version sets do not intersect.