use core::cmp::min;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::chain::cosmos::types::GasConfig;
use crate::config::GasPrice;

pub fn gas_amount_to_fees(config: &GasConfig, gas_amount: u64) -> Fee {
    let gas_limit = adjust_gas_with_simulated_fees(config, gas_amount);

    let amount = calculate_fee(gas_limit, &config.gas_price);

    Fee {
        amount: vec![amount],
        gas_limit,
        payer: "".to_string(),
        granter: "".to_string(),
    }
}

/// Adjusts the fee based on the configured `gas_adjustment` to prevent out of gas errors.
/// The actual gas cost, when a transaction is executed, may be slightly higher than the
/// one returned by the simulation.
pub fn adjust_gas_with_simulated_fees(config: &GasConfig, gas_amount: u64) -> u64 {
    let gas_adjustment = config.gas_adjustment;
    let max_gas = config.max_gas;

    let (_, digits) = mul_ceil(gas_amount, gas_adjustment).to_u64_digits();
    assert!(digits.len() == 1);

    let adjustment = digits[0];
    let gas = gas_amount.checked_add(adjustment).unwrap_or(u64::MAX);

    min(gas, max_gas)
}

pub fn calculate_fee(adjusted_gas_amount: u64, gas_price: &GasPrice) -> Coin {
    let fee_amount = mul_ceil(adjusted_gas_amount, gas_price.price);

    Coin {
        denom: gas_price.denom.to_string(),
        amount: fee_amount.to_string(),
    }
}

/// Multiply `a` with `f` and round the result up to the nearest integer.
pub fn mul_ceil(a: u64, f: f64) -> BigInt {
    assert!(f.is_finite());

    let a = BigInt::from(a);
    let f = BigRational::from_float(f).expect("f is finite");
    (f * a).ceil().to_integer()
}
