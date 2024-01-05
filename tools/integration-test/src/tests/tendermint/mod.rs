/// Juno v17.1.1 forces a 2 second block time, which causes this test
/// to fail.
/// https://github.com/CosmosContracts/juno/blob/v17.1.1/cmd/junod/cmd/root.go#L93
#[cfg(not(feature = "juno"))]
pub mod sequential;
