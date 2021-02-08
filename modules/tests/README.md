### Model-based testing

Let's say we want to test a system where:
- users can be created and deleted
- users have an id (say `u`)
- existing users have different ids

#### i. Testing
- sequence of actions and expected outcomes
    - `Test :: Vec<(Action, ActionOutcome)>`
    - __test a)__:
        - if I create user `u` (`action_1`), the operation should _succeed_ (`action_outcome_1`)
        - if then I delete user `u` (`action_2`), the operation should _succeed_ (`action_outcome_2`)
        - `Test = [(action_1, action_outcome_1), (action_2, action_outcome_2)]`
    - __test b)__:
        - if I create a user `u` (`action_1`), the operation should _succeed_ (`action_outcome_1`)
        - if I then I create user `u` (`action_2`), the operation should _fail_ with an `ExistingUser` error (`action_outcome_2`)
- let's say that an action + its expected outcome is a `Step`
    - `Step :: (Action, ActionOutcome)`
    - `Test :: Vec<Step>`


#### ii. Model

- what's a model?
    - it's description of a system 
    - in our case, it's a __description of the system under test__
- how do we write a model?
    - in a language called `TLA+`
- what do we do with a model?
    - e.g. prove invariants about it using a model checker
        - example of an invariant: "existing users have different ids"
        - model checkers for `TLA+`: `TLC` and `Apalache`

#### How do we join i. and ii.?

1. use the model to generate tests
    - let's say we want a test where some user is deleted successfully
        - define an invariant __negating the test__:
            - "it's not possible that a user is deleted successfully"
        - then we ask `Apalache` to prove it
        - because the invariant is false, `Apalache` will find a counter example that shows it
            - for example, it can find __test a)__
2. monitor the model
    - track each model action and its outcome
        - define two `TLA+` variables: `action` and `actionOutcome`