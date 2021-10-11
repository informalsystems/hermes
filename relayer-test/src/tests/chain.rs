use tracing::info;
use eyre::Report as Error;

use crate::init::init_test;
use crate::chain::builder::ChainBuilder;

#[test]
fn test_chain_manager() -> Result<(), Error> {
    init_test()?;

    let builder = ChainBuilder::new(
        "gaiad",
        "data",
    );

    let chain = builder.new_chain();

    info!("created new chain: {:?}", chain);

    chain.initialize()?;

    let validator_id_1 = chain.add_random_wallet("validator")?;
    let validator_id_2 = chain.add_random_wallet("validator")?;

    let user_id_1 = chain.add_random_wallet("user")?;
    let user_id_1 = chain.add_random_wallet("user")?;


    Ok(())
}
