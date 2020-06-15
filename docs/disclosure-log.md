# Disclosure Log for IBC Protocols

This document is a record of all the bugs or issues we uncovered while specifying & formally verifying the IBC protocols.


##### 1. ICS3 liveness problem due to ICS018 relayer algorithm

The algorithm for relaying connection handshake datagrams of type `ConnOpenTry`does not handle the situation when both chains are in state `INIT`.
The current relayer algorithm in [ICS018](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms) specifies that the `ConnOpenTry` datagram should be relayed only if one of the chains is in state `INIT` and the other chain is uninitialized (see the snippet below); this is not enough for guaranteeing liveness of the connection handshake protocol (ICS04).

```
    if (localEnd.state === INIT && remoteEnd === null)
```

The correct code should include both the cases when a single chain is in state `INIT`, as well as the case when both chains are in state `INIT`, as specified here: [Relayer.tla](https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Relayer.tla#L174)
This fix only concerns the relayer algorithm ICS018.

###### Channel handshake (ICS4) liveness problem

The same issue (and fix) seems to exist for the channel handshake datagrams.

##### 2. ICS3 liveness problem due to `UpdateClient` semantics

Related issues: [#71](https://github.com/informalsystems/ibc-rs/issues/71) and [#61](https://github.com/informalsystems/ibc-rs/issues/61).

Code for obtaining an execution trace in TLA+: [#73](https://github.com/informalsystems/ibc-rs/pull/73).
Briefly, this trace comprises the following sequence of actions, assuming two chains `A` and `B` and a relayer (as a simplification, the chains in this model are in charge of creating messages, a responsibility that the relayer typically implements):


0. Chain `A` creates a message `M` that has a proof for height `h`, chain `A` also advances its height to `h+1`.

1. The relayer updates the client on chain `B` with the latest height of chain A, namely `h+1` (call to `UpdateClient`).

2. The relayer sends message `M` that chain `A` created (at step 0) to chain B, and also attempt to update the client on chain `B` with height `h` (the height in the proof of this message), but is unable to do so because `h` is smaller than `h +1` (the latest height of client on chain B).

3. Chain `B` will be unable to verify message `M` since it lacks the adequate height information `h`, so chain `B` will drop this message, hence ICS3 can no longer progress.

For the full details of this trace, see the [README.md](https://github.com/informalsystems/ibc-rs/blob/e33f32db95314461d18fbdb13574ddeabafedad4/verification/spec/connection-handshake/updateclient-deadlock/README.md) within #73.