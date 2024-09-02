*September 2nd, 2024*

This release fixes an issue where Hermes could not connect to gRPC servers over TLS. Additionally, this release also fixes a bug in the `clear packet` CLI where the `excluded_sequences` configuration option was not always taken into account.

Furthermore, Hermes now uses `abci_query` instead of gRPC for some queries, for instance for querying staking parameters and service configuration during health checks, and when retrieving version information.
