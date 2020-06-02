# Disclosure Log for IBC Protocols

This document is a record of all the bugs or issues we uncovered while specifying & formally verifying the IBC protocols.


##### 1. ICS3 deadlock due to relayer algorithm

The algorithm for relaying connection handshake datagrams of type `ConnOpenTry`does not handle the situation when both chains are in state `INIT`. The current relayer algorithm in [ICS018](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms) specifies that the `ConnOpenTry` datagram should be relayed only if one of the chains is in state `INIT` and the other chain is uninitialized (see the snippet below) which can lead to a deadlock.

```
    if (localEnd.state === INIT && remoteEnd === null)
```

The correct code should include both the cases when a single chain is in state `INIT` and the case when both chains are in state `INIT`, as specified here: [Relayer.tla](https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Relayer.tla#L174)


##### 2. ICS3 deadlock due to `UpdateClient` semantics

Related issues: [#71](https://github.com/informalsystems/ibc-rs/issues/71) and [#61](https://github.com/informalsystems/ibc-rs/issues/61).

Code: [#73](https://github.com/informalsystems/ibc-rs/pull/73).
