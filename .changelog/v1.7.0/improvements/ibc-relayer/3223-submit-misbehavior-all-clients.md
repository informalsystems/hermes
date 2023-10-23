- When Hermes detects a misbehaviour from a on-chain client, eg. a light
  client attack or a double-sign, it will now submit the misbehaviour
  evidence to all counterparty clients of the misbehaving chain
  instead of to the counterparty client of the misbehaving client only.
  ([\#3223](https://github.com/informalsystems/hermes/issues/3223))