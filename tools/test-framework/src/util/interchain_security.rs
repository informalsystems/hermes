use ibc_relayer::config::ChainConfig;

use crate::{
    chain::config::set_voting_period,
    prelude::*,
};

pub fn update_genesis_for_consumer_chain(genesis: &mut serde_json::Value) -> Result<(), Error> {
    // Consumer chain doesn't have a gov key.
    if genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get("gov"))
        .is_some()
    {
        set_voting_period(genesis, 10)?;
    }
    Ok(())
}

pub fn update_relayer_config_for_consumer_chain(config: &mut Config) {
    // The `ccv_consumer_chain` must be `true` for the Consumer chain.
    // The `trusting_period` must be strictly smaller than the `unbonding_period`
    // specified in the Consumer chain proposal. The test framework uses 100s in
    // the proposal.
    for chain_config in config.chains.iter_mut() {
        match chain_config {
            ChainConfig::CosmosSdk(chain_config) | ChainConfig::Astria(chain_config)
                if chain_config.id == ChainId::from_string("ibcconsumer") =>
            {
                chain_config.ccv_consumer_chain = true;
                chain_config.trusting_period = Some(Duration::from_secs(99));
            }
            ChainConfig::CosmosSdk(_) | ChainConfig::Astria(_) => {}
        }
    }
}
