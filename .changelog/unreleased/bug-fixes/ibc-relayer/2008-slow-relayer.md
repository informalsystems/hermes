- Fix a bug which would cause the relayer to slow down exponentially when either
  the average block time was low or when it was relaying on too many chains at
  once ([#2008](https://github.com/informalsystems/ibc-rs/issues/2008))
