- When enabled for misbehaviour (ie. when `mode.misbehaviour.enabled = true`),
  Hermes monitors on-chain client updates and verifies the submitted
  headers comparing with headers it retrieves from its RPC node.
  If it detects conflicting headers, it submits a `MisbehaviourMsg`
  to the chain hosting the IBC client.
  In addition, Hermes will now also submit the evidence to the reference chain.
  ([\#3224](https://github.com/informalsystems/hermes/issues/3224))
