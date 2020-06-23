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
This light client requires, given item `X` at height `h` on `A`, a proof constructed at height `h-1`.
Put simply, the light client needs: (1) the item `X` at height `h` (as part of what is called "consensus state"), plus (2) a proof constructed at height `h-1` for this item.

2. __Concurrency:__ Different relayers may update the same light client. Suppose a relayer `r1` wants to submit `X` at consensus state `h` plus the associated proof at `h-1`.
In the meantime, however, another relayer `r2` may update this same light client to height `h'`.
It is important to note that `h'` is bigger than `h`.
Now `r1` will be unable to update the light client with consensus state `h`, because the light client disallows updates with smaller heights than the current height `h'`; consequently, the relayer will be unable to submit `X`.

To ensure eventual delivery, relayer `r1` would need to retry submitting item `X`, that is: resubmit the item at a larger height (e.g., at `h'`) with the associated proof (at `h'-1`).
This retry mechanism was adoped as a solution for the [current relayer implementation](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-002-ibc-relayer.md#ibc-client-consensus-state-vs-relayer-light-client-states-vs-chain-states).
Note that it is also possible for relayer `r2` to have submitted the same item `X` successfully; in this case, the liveness problem does not actually surface.


##### TLA+ trace

To obtain an execution in TLA+ that depicts the above liveness problem, it is sufficient to enable the `Concurrency` flag in the default TLA+ spec for ICS3.
In this spec we make a few simplifications compared to the real system, most importantly: to verify an item at height `h`, a light client can use the consensus state at the same height `h` (no need for smaller height `h-1`).
Below we summarize the parameters as well as the sequence of actions that lead to the liveness problem.

###### Parameters:

- `MaxBufLen <- 2`
- `MaxHeight <- 6`
- `Concurrency <- True`
- Behavior spec: Temporal formula `Spec`
- Check for `Deadlock`, Invariants `TypeInvariant` and `ConsistencyProperty`, as well as Property `Termination`

###### Trace:

Both chains `A` and `B` start at height `1`, and the light client on each chain has consensus state `1`.

1. The environment submits a `ICS3MsgInit` message to chain `A`.

2. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `1` to height `2`.

3. Chain `A` processes the `ICS3MsgInit`, advances to height `3`, and prepares a `ICS3MsgTry` message destined for chain `B`.
The proof in this message is for height `3`.

4. The environment triggers the `AdvanceChainHeight` action of chain `A`, so this chain transitions from height `3` to height `4`.

5. __Concurrency:__ The environment triggers the `UpdateClient` action on chain `B`: the light client on this chain is updated with height `4` (that is, the latest height of chain `A`), and chain `B` also transitions from height `1` to height `2`.

6. The environment passes (i.e., relays) the `ICS3MsgTry` message to chain `B`.
Recall that this message has proofs for height `3`; consenquently, the environment also attempts to trigger `UpdateClient` action on chain `B` for consensus state `3`.
This action does not enable because the light client on `B` has a more recent consensus state `4`.

7. Chain `B` attempts to process the `ICS3MsgTry` but is unable to verify its authenticity, since the light client on this chain does not have the required consensus state `3`.
Chain `B` drops this message.

From this point on, the model stutters, i.e., is unable to progress further in the connection handshake protocol.