# Disclosure Log for IBC Protocols

This document is a record of all the bugs or issues we uncovered while specifying & formally verifying the IBC protocols.


### 1. ICS3 liveness problem due to ICS018 relayer algorithm

The algorithm for relaying connection handshake datagrams of type `ConnOpenTry`does not handle the situation when both chains are in state `INIT`.
The current relayer algorithm in [ICS018](https://github.com/cosmos/ibc/tree/19f519b2d6829e3096d6b9f79bffb7836033e79c/spec/relayer/ics-018-relayer-algorithms) specifies that the `ConnOpenTry` datagram should be relayed only if one of the chains is in state `INIT` and the other chain is uninitialized (see the snippet below); this is not enough for guaranteeing liveness of the connection handshake protocol (ICS04).

```
    if (localEnd.state === INIT && remoteEnd === null)
```

The correct code should include both the cases when a single chain is in state `INIT`, as well as the case when both chains are in state `INIT`, as specified here: [Relayer.tla](https://github.com/informalsystems/hermes/blob/e1b78946529e39a5c709ccd6d11637993073164e/docs/spec/relayer/Relayer.tla#L174)
This fix only concerns the relayer algorithm ICS018.

##### Channel handshake (ICS4) liveness problem

The same issue (and fix) seems to exist for the channel handshake datagrams.


### 2. ICS3 liveness problem due to `UpdateClient` semantics

This problem is not specific to the connection handshake protocol (ICS3) itself, but is a bug in the way the relayers use the `UpdateClient` action.
We classify this under ICS3, however, since this is the context where we discovered the problem.
The TLA+ spec we have for depicting this liveness problem is for the ICS3 protocol.

##### Problem statement

Related issues: [#71](https://github.com/informalsystems/hermes/issues/71) and [#61](https://github.com/informalsystems/hermes/issues/61).
The problem is more thoroughly described in #61, but for the sake of completeness we restated it here in a compact form.

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
If the light client disallows updates with heights smaller than the current height `h'` then `r1`'s update fails.
Consequently, the relayer will be unable to submit consensus state at height `h`.

To ensure eventual delivery, relayer `r1` would need to retry submitting item `X`, that is: resubmit the consensus state at a larger height (e.g., at `h'`) followed by the message that includes the proof for `X` (e.g., at `h'-1`).
This retry mechanism was adopted as a solution for the [current relayer implementation](https://github.com/informalsystems/hermes/blob/master/docs/architecture/adr-002-ibc-relayer.md#ibc-client-consensus-state-vs-relayer-light-client-states-vs-chain-states).
Note that it is also possible for relayer `r2` to have submitted the same item `X` successfully; in this case, the liveness problem does not actually surface.


##### TLA+ trace

> Note that the TLA+ spec below may change in time. Here we refer to the spec as [existing at this commit](https://github.com/informalsystems/hermes/tree/788c36be9e14725c542bd586b4fe4593edb3ca80/docs/spec/connection-handshake/L2-tla) (unchanged up to [release 0.0.2](https://github.com/informalsystems/hermes/releases/tag/v0.0.2)).  

To obtain an execution in TLA+ that depicts the above liveness problem, it is sufficient to enable the `Concurrency` flag in the L2 default TLA+ spec for ICS3.
This spec is located in [spec/connection-handshake/L2-tla/](spec/connection-handshake/L2-tla/).
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
Recall that this message has proofs for height `2`; consequently, the environment also attempts to trigger `UpdateClient` action on chain `B` for consensus state at height `2`.
This action does not enable because the light client on `B` has a more recent consensus state for height `4`.

8. Chain `B` attempts to process the `ICS3MsgTry` but is unable to verify its authenticity, since the light client on this chain does not have the required consensus state at height `2`.
Chain `B` drops this message.

From this point on, the model stutters, i.e., is unable to progress further in the connection handshake protocol.


### 3. ICS3 problems due to version negotiation

__Context__.
The original issue triggering this discussion is here: [cosmos/ics/#459](https://github.com/cosmos/ibc/issues/459).
Briefly, version negotiation in the ICS3 handshake can interfere in various ways, breaking either the safety or liveness of this protocol.
Several solution candidates exist, which we classify by their "mode", i.e., a strategy for picking the version at some point or another in the protocol.
For a full description of the modes, please consult [L2-tla/readme.md#version-negotiation-modes](spec/connection-handshake/L2-tla/README.md#version-negotiation-modes).

__Overview__.
Below we use TLA+ traces to explore and report on the exact problems that can occur. We also show how the solution candidates fare.
The table below summarizes our results for the four cases we consider:

|	Case  |         Property violation |
|---------|----------------------------|
| (a) Empty version intersection | liveness|
| (b) Mode `overwrite`           | safety|
| (c) Mode `onTryNonDet`         | liveness|
| (d) Mode `onAckNonDet`         | safety|


These are the main takeaways from this discussion:

1. The set of compatible versions that chains start off with (return values of `getCompatibleVersions()` in ICS3) have to intersect, otherwise a liveness issue occurs. This assumption is independent of the version negotiation mode. We report this in __case (a)__ below.
2. Modes "overwrite", "onTryNonDet", and "onAckNonDet" all result in breaking the handshake protocol. See __cases (b), (c), and (d)__ below for traces.
3. The deterministic modes "onTryDet" and "onAckDet" pass model checking, so a solution should be chosen among these two candidates (see the [original issue](https://github.com/cosmos/ibc/issues/459) for follow-up on the solution).

##### Case (a). Empty version intersection causes liveness issue

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

Outcome:
- Model checking halts with exception "Temporal properties were violated."

###### Trace 

The two chains start off with different versions (`1` for A, and `2` for B).
So the __compatible version__ sets on these chains do not intersect.

1. The environment submits a `ICS3MsgInit` message chain `A`.

2. The environment triggers the `AdvanceChainHeight` action of chain `B`, so this chain transitions from height `1` to height `2`.

3. The environment triggers the `AdvanceChainHeight` action of chain `B`, so this chain transitions from height `2` to height `3`.

4. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `1` to height `2`.

5. Chain `A` processes the `ICS3MsgInit`, advances to height `3`, and prepares a `ICS3MsgTry` for chain `B`.
The version in this message is `<<1>>`, the same as the version field that chain `A` started with.

7. The environment relays the `ICS3MsgTry` message to the input buffer of chain `B`.
This message has proofs for height `3` so chain `B` gets updated with consensus state for height `4`.
With this update, chain `B` also advances to height `4`.

8. Chain `B` drops the `ICS3MsgTry` message because the version field does not match any of the compatible versions of this chain.
Therefore, the model cannot progress.

###### Fix

To fix this issue, the model requires an explicit assumption that the compatible versions on the two chains must have a non-empty intersection.
We capture this assumption in the `Init` action, via the `ChainVersionsOverlap` predicate:

```tla
Init ==
    /\ chmA!Init 
    /\ chmB!Init
    /\ ChainVersionsOverlap(storeChainA, storeChainB)
    /\ InitEnv  
```

Once we add the `ChainVersionsOverlap` assumptions, this model no longer has liveness issues.
But the "overwrite" mode can lead to safety problems, however, which we document below.

##### Case (b). Mode `overwrite` causes safety issue

Model checking details in TLA+:
- Model parameters:
```
Concurrency <- FALSE
MaxBufLen <- 2
MaxHeight <- 7
MaxVersionNr <- 2
VersionPickMode <- "overwrite"
```
- Check for invariant _VersionInvariant, as well as _Deadlock_ and property _Termination_.
- Make sure the `Init` action includes the `ChainVersionsOverlap` predicate.

Outcome:
- Model checking halts with exception "Invariant VersionInvariant is violated."

###### Trace 

Both chains `A` and `B` start with the compatible versions `<<1, 2>>`.

1. The environment submits a `ICS3MsgInit` message to both chains.

2. Chain `A` processes the `ICS3MsgInit`, advances to height `2`, and prepares a `ICS3MsgTry` for chain `B`.
The versions in this message are `<<1, 2>>`, the same as the version field in chain `A`.
The connection on this chain goes from state `UNINIT` to state `INIT`.

3. Chain `B` processes the `ICS3MsgInit`, advances to height `2`, and prepares a `ICS3MsgTry` for chain `A`.
The versions in this message are `<<1, 2>>`, the same as the version field in chain `B`.
The connection on this chain goes from state `UNINIT` to state `INIT`.

4. The environment relays the `ICS3MsgTry` message to the input buffer of chain `B`.
This message has proofs for height `2`, so the environment triggers `UpdateClient` on chain `B` for consensus state at height `2`.
With this update, chain `B` advances to height `3`.

5. The environment relays the `ICS3MsgTry` message to the input buffer of chain `A`.
This message has proofs for height `2`, so the environment triggers `UpdateClient` on chain `A` for consensus state at height `2`.
With this update, chain `A` advances to height `3`.

6. Chain `A` processes the `ICS3MsgTry` message, advances to height `4`, and prepares a `ICS3MsgAck` message for `B`.
The version in this message is `1`.
The connection in this chain goes into state `TRYOPEN`, with version chosen to be `1`.

7. Chain `B` processes the `ICS3MsgTry` message, advances to height `4`, and prepares a `ICS3MsgAck` message for `A`.
The version in this message is `2`.
The connection in this chain goes into state `TRYOPEN`, with version chosen to be `2`.

8. The environment relays the `ICS3MsgAck` message to the input buffer of chain `B`.
This message has proofs for height `4`, so the environment triggers `UpdateClient` on chain `B` for consensus state at height `4`.
With this update, chain `B` advances to height `5`.

9. Chain `B` processes the `ICS3MsgAck` message (which had version `1` -- see step 6 above), advances to height `6`, and prepares a `ICS3MsgConfirm` message for `A`.
Chain `B` overwrites its local version (namely, `2`) with the version in the `ICS3MsgAck` message (that is, `1`).
The connection in this chain goes into state `OPEN`, with version chosen to be `1`.
The `ICS3MsgConfirm` that chain `B` creates contains version `1`.

10. The environment relays the `ICS3MsgAck` message to the input buffer of chain `A`.
This message has proofs for height `4`, so the environment triggers `UpdateClient` on chain `A` for consensus state at height `4`.
With this update, chain `A` also advances to height `5`.

11. Chain `A` processes the `ICS3MsgAck` message; recall that the version in this message is `2` (see step 7 above).
Upon processing this message, chain `A` overwrites its local version (which was `1`) with the version in the `ICS3MsgAck` message (concretely, `2`).
The connection in this chain goes into state `OPEN`, with version chosen to be `2`.
Chain `A` also advances to height `6` and prepares a `ICS3MsgConfirm` message for `B`; the `ICS3MsgConfirm` contains version `2`.

At this point, the connection is `OPEN` at both chains, but the version numbers do not match.
Hence, the invariant `VersionInvariant` is violated.


##### Case (c). Mode `onTryNonDet` causes liveness issue

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
- The issue is that the version in the two chains diverges and can never reconcile

###### Trace

Both chains `A` and `B` start with the field `<<1, 2>>`, that is, with two compatible versions.

1. The environment submits a `ICS3MsgInit` message to both chains.

2. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `1` to height `2`.

3. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `2` to height `3`.

4. Chain `B` processes the `ICS3MsgInit`, advances to height `2`, and prepares a `ICS3MsgTry` message destined for chain `A`.
The versions in this message are `<<1, 2>>`, the same as the version field in chain `B`.

5. The environment triggers the `AdvanceChainHeight` action of chain `B`, so this chain transitions from height `2` to height `3`.

6. Chain `A` processes the `ICS3MsgInit`, advances to height `4`, and prepares a `ICS3MsgTry` message destined for chain `B`.
The versions in this message are `<<1, 2>>`, the same as the version field in chain `A`.

7. The environment passes (i.e., relays) the `ICS3MsgTry` message to the input buffer of chain `B`.
This message has proofs for height `4`; consequently, the environment also triggers `UpdateClient` on chain `B` for consensus state at height `4`, preparing this chain to process the message in the input buffer.
With this update, chain `B` advances to height `4`.

8. The environment passes (i.e., relays) the `ICS3MsgTry` message to the input buffer of chain `A`.
This message has proofs for height `2`, so the environment also does a `UpdateClient` on chain `A` for consensus state at height `2`.
With this update, chain `A` advances to height `5`.

9. Chain `A` processes the `ICS3MsgTry`, advances to height `6`, and prepares a `ICS3MsgAck` for chain `B`.
The version in this message is `<<2>>`, which is the version which chain `A` choose non-deterministically for this connection.
The connection on chain `A` is now in state `TRYOPEN`.

10. Chain `B` processes the `ICS3MsgTry`, advances to height `5`, and prepares a `ICS3MsgAck` for chain `A`.
The version in this message is `<<1>>`, which chain `B` choose non-deterministically for this connection.
The connection on chain `B` is now in state `TRYOPEN`.

From this point on, the two chains can not make further progress in the handshake, since they chose different versions.
Neither of the two chains can process the `ICS3MsgAck` message because the version in this message does not match with the version the chain stores locally.
(A chain should not overwrite its local version either, otherwise the safety issue from case (b) can appear.)
Therefore, the model stutters (cannot progress anymore).

##### Case (d). Mode `onAckNonDet` causes safety issue

Model checking details in TLA+:
- Model parameters:
```
Concurrency <- FALSE
MaxBufLen <- 2
MaxHeight <- 7
MaxVersionNr <- 2
VersionPickMode <- "onAckNonDet"
```
- Check for invariant _VersionInvariant, as well as _Deadlock_ and property _Termination_.

Outcome:
- Model checking halts with exception "Invariant VersionInvariant is violated."

###### Trace

Both chains `A` and `B` start with the compatible versions `<<1, 2>>`.

1. The environment submits a `ICS3MsgInit` message chain `A`.

2. Chain `A` processes the `ICS3MsgInit`, advances to height `2`, and prepares a `ICS3MsgTry` for chain `B`.
The versions in this message are `<<1, 2>>`, the same as the version field in chain `A`.
The connection on this chain goes from state `UNINIT` to state `INIT`.

3. The environment relays the `ICS3MsgTry` message to the input buffer of chain `B`.
This message has proofs for height `2`, so the environment triggers `UpdateClient` on chain `B` for consensus state at height `2`.
With this update, chain `B` advances to height `2`.

4. Chain `B` processes the `ICS3MsgTry` message, advances to height `3`, and prepares a `ICS3MsgAck` message for `A`.
The version in this message is `<<1, 2>>`.
The connection in this chain goes into state `TRYOPEN`; chain `B` does not choose a specific version yet, so the connection on `B` still has versions `<<1, 2>>`.

5. The environment relays the `ICS3MsgAck` message to the input buffer of chain `A`.
This message has proofs for height `3`, so the environment triggers `UpdateClient` on chain `A` for consensus state at height `3`.
With this update, chain `A` advances to height `3`.

6. Chain `A` processes the `ICS3MsgAck` message (which has versions `<<1, 2>>`), advances to height `4` and prepares a `ICS3MsgConfirm` message for `B`.
Chain `A` locks on version `1` (non-deterministic choice between `<<1, 2>>`), which it also reports in the `ICS3MsgConfirm` message.
The connection in this chain goes into state `OPEN`, with version chosen to `1`.

7. The environment relays the `ICS3MsgConfirm` message to the input buffer of chain `B`.
This message has proofs for height `4`, so the environment triggers `UpdateClient` on chain `B` for consensus state at height `4`.
With this update, chain `B` also advances to height `4`.

8. Chain `B` processes the `ICS3MsgConfirm` message (which contains version `1`).
Chain `B` locks on version `2` (non-deterministic choice between its local versions `<<1, 2>>`).
The connection in this chain goes into state `OPEN`.

At this point, the connection is `OPEN` at both chains, but the version numbers do not match.
Hence, the invariant `VersionInvariant` is violated.
