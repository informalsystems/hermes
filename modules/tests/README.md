## Model-based tests for IBC modules

### The model

This directory contains the model-based tests for the IBC modules. They are "model-based" because they are generated from a `TLA+` model of the IBC modules (see [IBC.tla](support/model_based/IBC.tla)).

To instantiate the model, we define in [IBC.cfg](support/model_based/IBC.cfg) the following model constants:
    - `ChainIds = {"chain-A", "chain-B"}`, indicating that two chains, `chain-A` and `chain-B`, will be created
    - `MaxClientsPerChain = 1`, indicating that at most 1 client per chain will be created
    - `MaxClientHeight = 2`, indicating that clients will reach at most height 2

The [IBC.cfg](support/model_based/IBC.cfg) file also defines two simple invariants:
```tla
INVARIANTS
    TypeOK
    ModelNeverErrors
```

Then, we can ask [`Apalache`](https://apalache.informal.systems), a model checker for `TLA+`, to check that these invariants hold:
```bash
apalache-mc check --inv=ICS02UpdateOKTestNeg IBC.tla
```

The above command automatically reads what we have defined in [IBC.cfg](support/model_based/IBC.cfg).

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

Then, we ask `Apalache`, to prove it:

```bash
apalache-mc check --inv=ICS02UpdateOKTestNeg IBCTests.tla
```

(Again, the above command automatically reads what we have defined in [IBCTests.cfg](support/model_based/IBCTests.cfg).)

Because the invariant is wrong, `Apalache` will find a counterexample showing that it is indeed possible that a client is sucessfully updated to a new height. This counterexample is our test.

### Current limitations

The counterexamples currently produced by `Apalache` are not easy to parse and have traditionally required tools like [`jsonatr`](https://github.com/informalsystems/jsonatr). Fortunately, [that will change soon](https://github.com/informalsystems/apalache/issues/530), and `Apalache` will be able to produce counterexamples like those in [support/model_based/tests/](support/model_based/tests/).
These are currently generated manually, but can be easily mapped to Rust (see [step.rs](step.rs)).

### Running the model-based tests

The model-based tests can be run with the following command:
 
```bash
cargo test -p ibc --features mocks -- model_based
```
