# IBC Connection Handshake (ICS3) TLA+ spec


This is a high-level TLA+ spec for the IBC Connection Handshake (ICS3) protocol.
The spec has three modules: 

  - `Environment.tla` (main model lives here).
  - `ICS3Module.tla` (the spec for the ICS3 module).
  - `ICS3Types.tla` (common domain definitions).


To run this spec:

1. add the three modules in a new specification in the toolbox
2. specify values for constants `MaxHeight`, `MaxBufLen`, and `Concurrency`.

Note the assumptions:

```
ASSUME MaxHeight > 1
ASSUME MaxBufLen >= 1
```

Typical values could be: `MaxHeight = 5` and `MaxBufLen = 2`.
The `Concurrency` flag enables/disables some non-determinsm of the environment,
specifically:

- if TRUE, then the environment can non-deterministically advance the height or update the light client of a chain.
This configuration simulates a liveness problem caused by the way `UpdateClient` is used by relayers, and will lead the model to stutter.
To be clear: the stuttering is not caused by a bug in the ICS3 protocol itself; this model simply captures the original (faulty) algorithms surrounding the ICS3 protocol.
See more details in the [disclosure log](https://github.com/informalsystems/ibc-rs/pull/83).
- if FALSE, then the model should check correctly.

3. add the invariant `ConsistencyInv` and `TypeInvariant` as well as the property (temporal formula) `Termination`.

4. run the model checker.