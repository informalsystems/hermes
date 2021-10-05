- Fix a bug introduced in Hermes v0.7.0 where tx simulations would fail on
  chains based on Cosmos SDK 0.42. This would cause Hermes to use the max
  gas specified in the config when submitted the tx, leading to high fees.
  ([#1345](https://github.com/informalsystems/ibc-rs/issues/1345))