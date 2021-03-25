## Model-based tests for IBC modules

### The model

This directory contains the model-based tests for the IBC modules. They are "model-based" because they are generated from a `TLA+` model of the IBC modules (see [IBC.tla](support/model_based/IBC.tla)).

To instantiate the model, we define in [IBC.cfg](support/model_based/IBC.cfg) the following model constants:

- `ChainIds = {"chain-A", "chain-B"}`, indicating that two chains, `chain-A` and `chain-B`, will be created
- `MaxChainHeight = 4`, indicating that each chain will reach at most height 4
- `MaxClientsPerChain = 1`, indicating that at most 1 client per chain will be created
- `MaxConnectionsPerChain = 1`, indicating that at most 1 connection per chain will be created

The [IBC.cfg](support/model_based/IBC.cfg) file also defines two simple invariants:
```tla
INVARIANTS
    TypeOK
    ModelNeverErrors
```

Then, we can ask [`TLC`](https://github.com/tlaplus/tlaplus), a model checker for `TLA+`, to check that these invariants hold:

```bash
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
java -cp tla2tools.jar tlc2.TLC IBC.tla -modelcheck -config IBC.cfg -workers auto
```

### The tests

Tests are `TLA+` assertions that describe the desired shape of the test (see [IBCTests.tla](support/model_based/IBCTests.tla)). One of the assertions in [IBCTests.tla](support/model_based/IBCTests.tla) is the following:

```tla
ICS02UpdateOKTest ==
    /\ actionOutcome = "ICS02UpdateOK"
```

This very simple assertion describes a test where the [model](support/model_based/IBC.tla) variable `actionOutcome` reaches the value `"ICS02UpdateOK"`, which occurs when a client is successfully updated to a new height (see [ICS02.tla](support/model_based/ICS02.tla)).

To generate a test from the `ICS02UpdateOKTest` assertion, we first define an invariant negating it:
```tla
ICS02UpdateOKTestNeg == ~ICS02UpdateOKTest
```

Then, we ask `TLC`, to prove it. Because the invariant is wrong, `TLC` will find a counterexample showing that it is indeed possible that a client is sucessfully updated to a new height. This counterexample is our test.

### Running the model-based tests

The model-based tests can be run with the following command:
 
```bash
cd modules/
cargo test --features mocks -- mbt
```

The above uses [`modelator`](https://github.com/informalsystems/modelator), a model-based testing tool.
One of the steps automated by `modelator` is the negation of TLA+ tests assertions mentioned earlier.

To debug possible issues with `modelator`, run instead:
```bash
RUST_LOG=modelator=trace cargo test --features mocks -- mbt
```
