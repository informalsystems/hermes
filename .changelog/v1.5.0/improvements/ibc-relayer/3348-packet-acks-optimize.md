- Only query for packet acknowledgments when there are packet
  commitments on the counterparty, otherwise the query would
  return all acknowledments on chain, which is excruciatingly slow
  ([\#3348](https://github.com/informalsystems/hermes/issues/3348))