# IBC Connection Handshake (CH) TLA+ spec


This is a high-level TLA+ spec for the IBC Connection Handshake (CH) protocol.
The spec has two modules: 

  - `Environment.tla` (main model lives here)
  - `ConnectionHandshakeModule.tla` (the spec for the IBC CH module)


To run this:

1. add the two modules in a new specification in the toolbox
2. specify values for constants MaxHeight and MaxBufLen

Note the assumptions:

```
ASSUME MaxHeight > 1
ASSUME MaxBufLen > 1
```

Typical values could be: `MaxHeight = 5` and `MaxBufLen = 2`.


3. add the invariant `ConsistencyInv` and the property (temporal formula) `Termination`

4. run the model checker.