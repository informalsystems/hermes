- Use the `ibc.core.connection.v1.ConnectionParams` gRPC query to retrieve `maxExpectedTimePerBlock` 
  and check it against the configured `max_block_time` instead of using the `/genesis` endpoint. 
  This improves both startup times and reliability for most chains.
  ([\#4143](https://github.com/informalsystems/hermes/issues/4143))