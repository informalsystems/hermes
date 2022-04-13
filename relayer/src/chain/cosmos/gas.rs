use core::cmp::min;
use core::fmt;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::chain::cosmos::types::gas::GasConfig;
use crate::config::GasPrice;

pub struct PrettyFee<'a>(pub &'a Fee);

pub fn gas_amount_to_fees(config: &GasConfig, gas_amount: u64) -> Fee {
    let adjusted_gas_limit = adjust_gas_with_simulated_fees(config, gas_amount);

    // The fee in coins based on gas amount
    let amount = calculate_fee(adjusted_gas_limit, &config.gas_price);

    Fee {
        amount: vec![amount],
        gas_limit: adjusted_gas_limit,
        payer: "".to_string(),
        granter: config.fee_granter.clone(),
    }
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

/// Adjusts the fee based on the configured `gas_adjustment` to prevent out of gas errors.
/// The actual gas cost, when a transaction is executed, may be slightly higher than the
/// one returned by the simulation.
fn adjust_gas_with_simulated_fees(config: &GasConfig, gas_amount: u64) -> u64 {
    let gas_adjustment = config.gas_adjustment;

    assert!(gas_adjustment <= 1.0);

    let (_, digits) = mul_ceil(gas_amount, gas_adjustment).to_u64_digits();
    assert!(digits.len() == 1);

    let adjustment = digits[0];
    let gas = gas_amount.checked_add(adjustment).unwrap_or(u64::MAX);

    min(gas, config.max_gas)
}

impl fmt::Display for PrettyFee<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let amount = match self.0.amount.get(0) {
            Some(coin) => format!("{}{}", coin.amount, coin.denom),
            None => "<no amount specified>".to_string(),
        };

        f.debug_struct("Fee")
            .field("amount", &amount)
            .field("gas_limit", &self.0.gas_limit)
            .finish()
    }
}
