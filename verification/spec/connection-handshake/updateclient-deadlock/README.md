# ICS3 Protocol Deadlock Scenario

In this folder we describe a version of the ICS3 TLA+ specification that exhibits a deadlock, caused by a race condition in the way `UpdateClient` action is used.

There are three parts to this document:

- [A brief description of the ICS3 spec that can deadlock](#specification-details),

- [An annotated trace of a deadlocking execution](#trace).

### Specification details

This specification resembles closely the default spec, so it includes three modules: `Environment`, `ConnectionHandshakeModule`, and `ICS3Types`.

There are two main difference between this "deadlocking" version of the ICS3 protocol and the default specification: 
1. The default spec allows a client on a chain to be updated with arbitrary heights, whereas this deadlocking version enforces that client updates must be monotonic.
`UpdateClient` is the action that specifies a client update, and the specific precondition for this action in the "deadlocking version" is as follows:

```
CanUpdateClient(height) ==
    /\ CanAdvance
    /\ height \notin store.client.consensusHeights
    (* Warning: following line could provoke a deadlock in ICS3 protocol. *)
    /\ height >= store.client.latestHeight
```

The relevant part is the last line of this state predicate, requiring that the new height must be larger or equal than the latest height on the client.

2. The Environment in the default spec is non-deterministic, by comprising a sub-action `DefaultNextEnv` that can simply advance the height or update the client of one of the chains non-deterministically.
In contrast, the "deadlocking" version replaces this non-determinism in the Environment with a deterministic `UpdateChainClient` sub-action; this sub-action always update the client on one of the chains if that chain is expecting an incoming message, and otherwise the sub-action is not enabled.

The rationale behind the `UpdateChainClient` is that this sub-action should trigger before any relaying is performed, which can lead to the following problematic execution trace:

0. Chain A creates a message `M` that has a proof for height `h`, chain A also advances its height to `h+1`.

1. We update the client on chain B with the latest height of chain A, namely `h+1`; this is the `UpdateChainClient` deterministic sub-action.

2. We relay message `M` that chain A created (at step 0) to chain B, and also attempt to update the client on chain B with height `h` (the height in the proof of this message), but are unable to do so because `h` is smaller than  `h +1` (the latest height of client on chain B).

3. Chain B will be unable to verify message `M` since it lacks the adequate height information `h`, so chain B will drop this message, hence a deadlock occurs.


#### On the termination property

As a technical side-note, we simplify the termination property for this variant of the specification.
In the default spec, the non-determinism of `DefaultNextEnv` can make each chain advance their respective heights until they reach `MaxHeight`, and thereby becoming unable to progress any further and eventually open a connection.
For this reason, the termination property in the default spec has a precondition that each chain has not exhausted their steps, and are at least 4 steps away from `MaxHeight` (4 steps are minimum for completing the connection handshake).

In the deadlocking version, we can expect termination to always happen.
No preconditions are necessary for the termination property, since the environment non-determinism no longer exists.
We capture the termination conditions as follows:

```
<> [](/\ storeChainA.connection.state = "OPEN"
      /\ storeChainB.connection.state = "OPEN"))
```

### Trace


The following is an annotated trace of an execution that exhibits the deadlock.
To recreate this trace, simply import the three modules in your TLA+ toolbox and use the model as described in [MC.cfg](./MC.cfg) and [MC.tla](./MC.tla).

#### Annotated execution trace

    <<
    [
     _TEAction |-> [
       position |-> 1,
       name |-> "Initial predicate",
       location |-> "Unknown location"
     ],
     inBufChainA |-> << [ type |-> "ICS3MsgInit",
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
               remoteEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"] ] ] >>,
     inBufChainB |-> <<>>,
     outBufChainA |-> <<>>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 1,
      connection |->
          [ state |-> "UNINIT",
            parameters |->
                [ localEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ],
                  remoteEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ],
     storeChainB |-> [ latestHeight |-> 1,
      connection |->
          [ state |-> "UNINIT",
            parameters |->
                [ localEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ],
                  remoteEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ]
    ],

In this first step of the execution trace, the connection on both chains is in "UNINIT" state, and chain A is assigned the initialization message: see `inBufChainA` variable and the record with type `ICS3MsgInit` therein.

    [
     _TEAction |-> [
       position |-> 2,
       name |-> "Next",
       location |-> "line 285, col 8 to line 285, col 62 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> <<>>,
     outBufChainA |-> << [ type |-> "ICS3MsgTry",
         proofHeight |-> 1,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
               remoteEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"] ],
         connProof |->
             [ connection |->
                   [ state |-> "INIT",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ],
                           remoteEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ] ] ] ],
         clientProof |-> [latestHeight |-> 1, consensusHeights |-> {1}] ] >>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ],
     storeChainB |-> [ latestHeight |-> 1,
      connection |->
          [ state |-> "UNINIT",
            parameters |->
                [ localEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ],
                  remoteEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ]
    ],

In the second step, chain A finished processing the Init message and produces as output a `ICS3MsgTry` message.
As part of this step, chain A also advances its height to `2`.

    [
     _TEAction |-> [
       position |-> 3,
       name |-> "NextEnv",
       location |-> "line 230, col 8 to line 231, col 27 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> <<>>,
     outBufChainA |-> << [ type |-> "ICS3MsgTry",
         proofHeight |-> 1,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
               remoteEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"] ],
         connProof |->
             [ connection |->
                   [ state |-> "INIT",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ],
                           remoteEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ] ] ] ],
         clientProof |-> [latestHeight |-> 1, consensusHeights |-> {1}] ] >>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> TRUE,
     storeChainA |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ],
     storeChainB |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "UNINIT",
            parameters |->
                [ localEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ],
                  remoteEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ],

At the end of step 3 of this execution, the client on chain B is updated with the latest height of chain A (namely, height `2`).
See `client` record as part of the `storeChainB` variable.
At the same time, the height of chain B also advances from `1` to `2` (see `storeChainB |-> [ latestHeight |-> 2`).

    [
     _TEAction |-> [
       position |-> 4,
       name |-> "RelayNextEnv",
       location |-> "line 195, col 11 to line 202, col 73 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> << [ type |-> "ICS3MsgTry",
         proofHeight |-> 1,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
               remoteEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"] ],
         connProof |->
             [ connection |->
                   [ state |-> "INIT",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ],
                           remoteEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ] ] ] ],
         clientProof |-> [latestHeight |-> 1, consensusHeights |-> {1}] ] >>,
     outBufChainA |-> <<>>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ],
     storeChainB |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "UNINIT",
            parameters |->
                [ localEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ],
                  remoteEnd |->
                      [ connectionID |-> "NULLConnectionID",
                        clientID |-> "NULLClientID" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ],

At step 4, a relay sub-action is performed: the `ICS3MsgTry` message that chain A has produced earlier is moved into the input buffer of chain B.

    [
     _TEAction |-> [
       position |-> 5,
       name |-> "Next",
       location |-> "line 286, col 8 to line 286, col 62 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> <<>>,
     outBufChainA |-> <<>>,
     outBufChainB |-> << [ type |-> "ICS3MsgAck",
         proofHeight |-> 2,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
               remoteEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"] ],
         connProof |->
             [ connection |->
                   [ state |-> "TRYOPEN",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ],
                           remoteEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ] ] ] ],
         clientProof |-> [latestHeight |-> 2, consensusHeights |-> {1, 2}] ] >>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 2,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 1,
            consensusHeights |-> {1} ] ],
     storeChainB |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "TRYOPEN",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
                  remoteEnd |->
                      [ connectionID |-> "connAtoB",
                        clientID |-> "clientOnAToB" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ],

At the end of this step, chain B finished processing the `ICS3MsgTry` message and produced a `ICS3MsgAck` message.
It is important to note that the height of the proof in this Ack message is `2` (see `proofHeight |-> 2`).
Additionally, chain B also advanced from height `2` to `3`.

    [
     _TEAction |-> [
       position |-> 6,
       name |-> "NextEnv",
       location |-> "line 230, col 8 to line 231, col 27 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> <<>>,
     outBufChainA |-> <<>>,
     outBufChainB |-> << [ type |-> "ICS3MsgAck",
         proofHeight |-> 2,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
               remoteEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"] ],
         connProof |->
             [ connection |->
                   [ state |-> "TRYOPEN",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ],
                           remoteEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ] ] ] ],
         clientProof |-> [latestHeight |-> 2, consensusHeights |-> {1, 2}] ] >>,
     relayToA |-> TRUE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 3,
            consensusHeights |-> {1, 3} ] ],
     storeChainB |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "TRYOPEN",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
                  remoteEnd |->
                      [ connectionID |-> "connAtoB",
                        clientID |-> "clientOnAToB" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ],

At the end of step 6, the client on chain A is updated with the latest height of chain B, consequently, this client will store the set of heights: `consensusHeights |-> {1, 3}`.

    [
     _TEAction |-> [
       position |-> 7,
       name |-> "RelayNextEnv",
       location |-> "line 207, col 11 to line 214, col 73 of module Environment"
     ],
     inBufChainA |-> << [ type |-> "ICS3MsgAck",
         proofHeight |-> 2,
         parameters |->
             [ localEnd |->
                   [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
               remoteEnd |->
                   [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"] ],
         connProof |->
             [ connection |->
                   [ state |-> "TRYOPEN",
                     parameters |->
                         [ localEnd |->
                               [ connectionID |-> "connBtoA",
                                 clientID |-> "clientOnBToA" ],
                           remoteEnd |->
                               [ connectionID |-> "connAtoB",
                                 clientID |-> "clientOnAToB" ] ] ] ],
         clientProof |-> [latestHeight |-> 2, consensusHeights |-> {1, 2}] ] >>,
     inBufChainB |-> <<>>,
     outBufChainA |-> <<>>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 3,
            consensusHeights |-> {1, 3} ] ],
     storeChainB |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "TRYOPEN",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
                  remoteEnd |->
                      [ connectionID |-> "connAtoB",
                        clientID |-> "clientOnAToB" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ],

We now perform a relay step, moving the `ICS3MsgAck` from the output buffer of chain B into the input buffer of chain A.
As part of relaying, the client on chain A is also updated (if possible) with the height that is reported in the proof from this messages, namely, height `2`.
This update is skipped, however, since the client on chain A already stores a higher height `3` (the update for this height occured earlier at step 6).

    [
     _TEAction |-> [
       position |-> 8,
       name |-> "Next",
       location |-> "line 285, col 8 to line 285, col 62 of module Environment"
     ],
     inBufChainA |-> <<>>,
     inBufChainB |-> <<>>,
     outBufChainA |-> <<>>,
     outBufChainB |-> <<>>,
     relayToA |-> FALSE,
     relayToB |-> FALSE,
     storeChainA |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "INIT",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connAtoB", clientID |-> "clientOnAToB"],
                  remoteEnd |->
                      [ connectionID |-> "connBtoA",
                        clientID |-> "clientOnBToA" ] ] ],
      chainID |-> "chainA",
      client |->
          [ clientID |-> "clientOnAToB",
            latestHeight |-> 3,
            consensusHeights |-> {1, 3} ] ],
     storeChainB |-> [ latestHeight |-> 3,
      connection |->
          [ state |-> "TRYOPEN",
            parameters |->
                [ localEnd |->
                      [connectionID |-> "connBtoA", clientID |-> "clientOnBToA"],
                  remoteEnd |->
                      [ connectionID |-> "connAtoB",
                        clientID |-> "clientOnAToB" ] ] ],
      chainID |-> "chainB",
      client |->
          [ clientID |-> "clientOnBToA",
            latestHeight |-> 2,
            consensusHeights |-> {1, 2} ] ]
    ]
    >>

At the final step, chain A effectively drops the `ICS3MsgAck` message since it cannot verify the proof (`proofHeight |-> 2,`) in this message.