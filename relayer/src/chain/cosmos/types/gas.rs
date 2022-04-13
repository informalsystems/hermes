use ibc_proto::cosmos::tx::v1beta1::Fee;

use crate::chain::cosmos::calculate_fee;
use crate::config::{ChainConfig, GasPrice};

/// Default gas limit when submitting a transaction.
const DEFAULT_MAX_GAS: u64 = 400_000;

/// Fraction of the estimated gas to add to the estimated gas amount when submitting a transaction.
const DEFAULT_GAS_PRICE_ADJUSTMENT: f64 = 0.1;

const DEFAULT_FEE_GRANTER: &str = "";

pub struct GasConfig {
    pub default_gas: u64,
    pub max_gas: u64,
    pub gas_adjustment: f64,
    pub gas_price: GasPrice,
    pub max_fee: Fee,
    pub fee_granter: String,
}

impl GasConfig {
    pub fn from_chain_config(config: &ChainConfig) -> GasConfig {
        GasConfig {
            default_gas: default_gas_from_config(config),
            max_gas: max_gas_from_config(config),
            gas_adjustment: gas_adjustment_from_config(config),
            gas_price: config.gas_price.clone(),
            max_fee: max_fee_from_config(config),
            fee_granter: fee_granter_from_config(config),
        }
    }
}

/// The default amount of gas the relayer is willing to pay for a transaction,
/// when it cannot simulate the tx and therefore estimate the gas amount needed.
pub fn default_gas_from_config(config: &ChainConfig) -> u64 {
    config
        .default_gas
        .unwrap_or_else(|| max_gas_from_config(config))
}

/// The maximum amount of gas the relayer is willing to pay for a transaction
pub fn max_gas_from_config(config: &ChainConfig) -> u64 {
    config.max_gas.unwrap_or(DEFAULT_MAX_GAS)
}

/// The gas price adjustment
fn gas_adjustment_from_config(config: &ChainConfig) -> f64 {
    config
        .gas_adjustment
        .unwrap_or(DEFAULT_GAS_PRICE_ADJUSTMENT)
}

/// Get the fee granter address
fn fee_granter_from_config(config: &ChainConfig) -> String {
    config
        .fee_granter
        .as_deref()
        .unwrap_or(DEFAULT_FEE_GRANTER)
        .to_string()
}

fn max_fee_from_config(config: &ChainConfig) -> Fee {
    let max_gas = max_gas_from_config(config);

    // The maximum fee the relayer pays for a transaction
    let max_fee_in_coins = calculate_fee(max_gas, &config.gas_price);

    let fee_granter = fee_granter_from_config(config);

    Fee {
        amount: vec![max_fee_in_coins],
        gas_limit: max_gas,
        payer: "".to_string(),
        granter: fee_granter,
    }
}
