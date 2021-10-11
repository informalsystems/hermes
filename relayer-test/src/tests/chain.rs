use tracing::info;
use eyre::Report as Error;
use core::time::Duration;

use crate::chain::config;
use crate::init::init_test;
use crate::chain::builder::ChainBuilder;
use crate::chain::bootstrap::bootstrap_chain;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new(
        "gaiad",
        "data",
    );

    let chain_a = bootstrap_chain(&builder)?;
    let chain_b = bootstrap_chain(&builder)?;

    Ok(())
}
