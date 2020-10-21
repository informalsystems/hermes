# IBC Connection Handshake (ICS3) TLA+ spec


This is a high-level TLA+ spec for the IBC Connection Handshake (ICS3) protocol.
The spec has four modules:

  - `Environment.tla` (main model lives here).
  - `ICS3Module.tla` (the spec for the ICS3 module).
  - `ICS3Types.tla` (common domain definitions).
  - `ICS3Utils.tla` (common actions live here).

To run this spec:

1. add the modules in a new specification in the toolbox
2. specify values for constants `MaxHeight`, `MaxBufLen`, and `Concurrency`.
Two additional constants serve the version negotiation algorithm in the handshake:
    - `MaxVersionNr` -- typical value `2`; or set to `1` to make version negotiation trivial;
    - `VersionPickMode` -- typical value `"onAckDet"`; parametrizes the strategy for negotiating versions (see [below](#version-negotiation-modes)).

Note the assumptions:

```
ASSUME MaxHeight > 4
ASSUME MaxBufLen >= 1
ASSUME VersionPickMode \in
    {"overwrite",
    "onTryDet",
    "onTryNonDet",
    "onAckDet",
    "onAckNonDet"}
```

Typical values could be: `MaxHeight = 5` and `MaxBufLen = 2`.
The `Concurrency` flag enables/disables some non-determinsm of the environment,
specifically:

- if TRUE, then the environment can non-deterministically update the light client of a chain.
This configuration simulates a liveness problem caused by the way relayers use `UpdateClient`, and will lead the model to stutter.
To be clear: the stuttering is not caused by a bug in the ICS3 protocol itself; this model simply captures the original faulty relayer algorithms surrounding the ICS3 protocol.
See more details in the [disclosure log](https://github.com/informalsystems/ibc-rs/pull/83).
- if FALSE, then the model should check correctly.

3. add the invariant `ConsistencyInv` and `TypeInvariant` as well as the property (temporal formula) `Termination`.

4. run the model checker.

## Version negotiation modes

We introduce different version picking modes, which are used to parameterize the way in which versions are picked during the connection handshake. That is, the constant `VersionPickMode` can take one of the following values:
 - `overwrite` : a version is picked non-deterministically when handling `ICS3MsgTry`, local version gets overwritten with version(s) sent in datagrams;
 - `onTryNonDet` : a version is picked non-deterministically when handling `ICS3MsgTry`, local version is chosen from intersection of local and datagram versions;
 - `onTryDet` : a version is picked deterministically when handling `ICS3MsgTry`, local version is chosen from intersection of local and datagram versions;
 - `onAckNonDet` : a version is picked non-deterministically when handling `ICS3MsgAck`, local version is chosen from intersection of local and datagram versions;
 - `onAckDet` : a version is picked non-deterministically when handling `ICS3MsgAck`, local version is chosen from intersection of local and datagram versions.
 
 The table below details these modes:

|	Mode\Action  |	`HandleMsgTry(m)`					              |	`HandleMsgAck(m)` 					|	`HandleMsgConfirm(m)`       |
|-------------|-----------------------------------------|-----------------------------|-----------------------------|
|`overwrite`  | pick a version from `m.versions \intersect conn.versions` non-deterministically, send the picked version to counterparty in `ICS3MsgAck` | store `m.version` locally, send it to counterparty in `ICS3MsgConfirm` | store `m.version` locally |
|`onTryNonDet`| pick a version from  `m.versions \intersect conn.versions` non-deterministically, send the picked version to counterparty in `ICS3MsgAck` | check if received version in `ICS3MsgAck` is in list of local versions, accept it if it is, send it to counterparty in `ICS3MsgConfirm` | check if received version is the same as one stored in connection end|
|`onTryDet`	  | pick a version from `m.versions \intersect conn.versions` deterministically (e.g. maximum), store & send the picked version to counterparty in `ICS3MsgAck` | check if received version in `ICS3MsgAck` is in list of local versions, accept & store it if it is, then send it to counterparty in `ICS3MsgConfirm` | check if received version is the same as one stored in connection end|
|`onAckNonDet`| send the value of `m.versions \intersect conn.versions` to counterparty in `ICS3MsgAck`, store the intersection locally | pick a version from `m.versions \intersect conn.versions` non-deterministically, send the intersection to counterparty in `ICS3MsgConfirm` | pick a version from `conn.versions` non-deterministically |
|`onAckDet`| send the value of the intersection `m.versions \intersect conn.versions` to counterparty in `ICS3MsgAck`, store the intersection locally | pick a version from `m.versions \intersect conn.versions` deterministically (e.g. maximum), send the intersection to counterparty in `ICS3MsgConfirm` | pick a version from `conn.versions` deterministically (e.g. maximum)|
