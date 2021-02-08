## Model-based tests for IBC modules

This directory contains the model-based tests for the IBC modules. They are "model-based" because they are generated from a `TLA+` model of the IBC modules (see [IBC.tla](IBC.tla)).

Tests are `TLA+` assertions that describe the desired shape of the test. One of the assertions in [IBCTests.tla](IBCTests.tla) is the following:

```tla
ICS02UpdateOKTest ==
    /\ actionOutcome = "ICS02UpdateOK"
```

This very simple assertion describes a test where the [model](IBC.tla) variable `actionOutcome` reaches the value `"ICS02UpdateOK"`, which occurs when a light client is successfully updated to a new height (see [ICS02.tla](ICS02.tla)).

To generate a test from the `ICS02UpdateOKTest` assertion, we first define an invariant negating it:
```tla
ICS02UpdateOKTestNeg == ~ICS02UpdateOKTest
```

Then, we ask [`Apalache`](https://apalache.informal.systems), a model checker for `TLA+`, to prove it:

```bash
apalache-mc check --inv=ICS02UpdateOKTestNeg IBCTests.tla
```

Because the invariant is wrong, `Apalache` will find a counterexample showing that it is indeed possible that a light-client is sucessfully updated to a new height. This counterexample is our test.

### Current limitations

The counterexamples currently produced by `Apalache` are not easy to parse and have traditionally required tools like [`jsonatr`](https://github.com/informalsystems/jsonatr). Fortunately, [that will change soon](https://github.com/informalsystems/apalache/issues/530), and `Apalache` will be able to produce counterexamples (like those in [tests/](tests/), which are currently generated manually) that can be easily mapped to Rust (see [step.rs](../../step.rs)).

### Running the model-based tests

The model-based tests can be run with the following command:
 
```bash
cargo test -p ibc --features mocks -- model_based
```
