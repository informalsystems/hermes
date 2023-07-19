- Add a new trait `InterchainSecurityChainTest` and two functions
  `run_binary_interchain_security_node_test` and `run_binary_interchain_security_channel_test`
  which can be used to bootstrap a Provider and Consumer chain for integration tests.
  Add a CI job to run tests with Gaia as a provider chain and Neutron as a Consumer chain.
  ([\#3450](https://github.com/informalsystems/hermes/issues/3450))
  ([\#3387](https://github.com/informalsystems/hermes/issues/3387))