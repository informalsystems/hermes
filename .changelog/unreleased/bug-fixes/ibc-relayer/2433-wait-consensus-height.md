- For the `ConnOpenTry` and `ConnOpenAck` steps, wait for the destination
  app height to be higher than the consensus height, otherwise we fail to
  complete the handshake when the block times of the two chains involved differ
  significantly ([#2433](https://github.com/informalsystems/ibc-rs/issues/2433))