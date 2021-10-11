use serde_json as json;
use tracing::info;
use eyre::{eyre, Report as Error};

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

    let validator1 = chain.add_random_wallet("validator")?;
    let validator2 = chain.add_random_wallet("validator")?;

    let user1 = chain.add_random_wallet("user")?;
    let user2 = chain.add_random_wallet("user")?;

    info!("created user {:?}", user1);

    chain.add_genesis_account(&validator1.address, &[
        ("stake", 1_000_000_000_000),
    ])?;

    chain.add_genesis_validator(&validator1.id, "stake", 1_000_000_000_000)?;

    chain.add_genesis_account(&user1.address, &[
        ("stake", 1_000_000_000_000),
        ("samoleans", 1_000_000_000_000)
    ])?;

    chain.collect_gen_txs()?;

    chain.update_chain_config(|mut config| {
        config.get_mut("rpc")
            .ok_or_else(|| eyre!("expect rpc section"))?
            .as_table_mut()
            .ok_or_else(|| eyre!("expect object"))?
            .insert("laddr".to_string(),
                format!("tcp://0.0.0.0:{}", chain.rpc_port).into());

        config.get_mut("p2p")
            .ok_or_else(|| eyre!("expect p2p section"))?
            .as_table_mut()
            .ok_or_else(|| eyre!("expect object"))?
            .insert("laddr".to_string(),
                format!("tcp://0.0.0.0:{}", chain.p2p_port).into());

        Ok(config)
    })?;

    let _child = chain.start()?;

    std::thread::sleep(std::time::Duration::from_secs(3));

    let balance = chain.query_balance(&user1.address, "samoleans")?;

    info!("user1 balance: {}", balance);

    // std::thread::sleep(std::time::Duration::from_secs(15));

    Ok(())
}
