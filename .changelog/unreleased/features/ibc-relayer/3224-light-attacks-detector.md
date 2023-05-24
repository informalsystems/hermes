t - When enabled for misbehaviour (ie. when `mode.misbehaviour.enabled = true`),
  Hermes will now monitors on-chain client updates and verify the submitted
  headers comparing with headers it retrieves from its RPC node.
  If it detects conflicting headers, it will now submit a `MisbehaviourMsg`
  to the chain hosting the IBC client.
  In addition, Hermes will also submit the evidence to the reference chain.
  ([\#3224](https://github.com/informalsystems/hermes/issues/3224))
