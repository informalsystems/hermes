- Fix a regression where Hermes would not retry relaying packet on account
  mismatch error when the sequence number used was smaller than the expected one
  ([#2411](https://github.com/informalsystems/ibc-rs/issues/2411))