use ibc_proto::cosmos::tx::v1beta1::Fee;

use crate::chain::cosmos::calculate_fee;
use crate::config::{ChainConfig, GasPrice};

/// Default gas limit when submitting a transaction.
const DEFAULT_MAX_GAS: u64 = 400_000;

/// Fraction of the estimated gas to add to the estimated gas amount when submitting a transaction.
const DEFAULT_GAS_PRICE_ADJUSTMENT: f64 = 0.1;

pub struct GasConfig {
    pub default_gas: u64,
    pub max_gas: u64,
    pub gas_adjustment: f64,
    pub gas_price: GasPrice,
    pub max_fee: Fee,
}

impl GasConfig {
    pub fn from_chain_config(config: &ChainConfig) -> GasConfig {
        GasConfig {
            default_gas: default_gas_from_config(config),
            max_gas: max_gas_from_config(config),
            gas_adjustment: gas_adjustment_from_config(config),
            gas_price: config.gas_price.clone(),
            max_fee: max_fee_from_config(config),
        }
    }
}

pub fn default_gas_from_config(config: &ChainConfig) -> u64 {
    config
        .default_gas
        .unwrap_or_else(|| max_gas_from_config(config))
}

pub fn max_gas_from_config(config: &ChainConfig) -> u64 {
    config.max_gas.unwrap_or(DEFAULT_MAX_GAS)
}

pub fn gas_adjustment_from_config(config: &ChainConfig) -> f64 {
    config
        .gas_adjustment
        .unwrap_or(DEFAULT_GAS_PRICE_ADJUSTMENT)
}

pub fn max_fee_from_config(config: &ChainConfig) -> Fee {
    let gas_limit = max_gas_from_config(config);
    let amount = calculate_fee(gas_limit, &config.gas_price);

    Fee {
        amount: vec![amount],
        gas_limit,
        payer: "".to_string(),
        granter: "".to_string(),
    }
}
