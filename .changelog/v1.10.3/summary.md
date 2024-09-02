*September 2nd, 2024*

This release brings several important updates and improvements across multiple components. Notably, it introduces explicit root TLS configuration for gRPC clients in both the Chain Registry and Relayer Library, enhancing security and configuration flexibility. Additionally, the Relayer CLI has been refined to ensure proper filtering of sequences in the clear packet command, improving the reliability of packet management.

Furthermore, the Relayer Library now uses `abci_query` instead of gRPC queries for staking parameters and service configuration during health checks, and when retrieving version information. These updates contribute to a more robust and efficient relayer experience.
