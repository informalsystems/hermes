use core::cmp::min;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::chain::cosmos::types::gas::GasConfig;
use crate::config::GasPrice;

pub fn gas_amount_to_fee(config: &GasConfig, gas_amount: u64) -> Fee {
    let adjusted_gas_limit = adjust_estimated_gas(AdjustGas {
        gas_multiplier: config.gas_multiplier,
        max_gas: config.max_gas,
        gas_amount,
    });

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

/// Multiply `a` with `f` and round the result down to the nearest integer.
pub fn mul_floor(a: u64, f: f64) -> BigInt {
    assert!(f.is_finite());

    let a = BigInt::from(a);
    let f = BigRational::from_float(f).expect("f is finite");
    (f * a).floor().to_integer()
}

struct AdjustGas {
    gas_multiplier: f64,
    max_gas: u64,
    gas_amount: u64,
}

/// Adjusts the fee based on the configured `gas_multiplier` to prevent out of gas errors.
/// The actual gas cost, when a transaction is executed, may be slightly higher than the
/// one returned by the simulation.
fn adjust_estimated_gas(
    AdjustGas {
        gas_multiplier,
        max_gas,
        gas_amount,
    }: AdjustGas,
) -> u64 {
    // No need to compute anything if the gas amount is zero
    if gas_amount == 0 {
        return 0;
    };

    // If the multiplier is 1, no need to perform the multiplication
    if gas_multiplier == 1.0 {
        return min(gas_amount, max_gas);
    }

    // Multiply the gas estimate by the gas_multiplier option
    let (_sign, digits) = mul_floor(gas_amount, gas_multiplier).to_u64_digits();

    let gas = match digits.as_slice() {
        // If there are no digits it means that the resulting amount is zero.
        [] => 0,

        // If there is a single "digit", it means that the result fits in a u64, so we can use that.
        [gas] => *gas,

        // Otherwise, the multiplication overflow and we use u64::MAX instead.
        _ => u64::MAX,
    };

    // Bound the gas estimate by the max_gas option
    min(gas, max_gas)
}

#[cfg(test)]
mod tests {
    use super::{adjust_estimated_gas, AdjustGas};

    #[test]
    fn adjust_zero_gas() {
        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier: 1.1,
            max_gas: 1_000_000,
            gas_amount: 0,
        });

        assert_eq!(adjusted_gas, 0);
    }

    #[test]
    fn adjust_gas_one() {
        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier: 1.0,
            max_gas: 1_000_000,
            gas_amount: 400_000,
        });

        assert_eq!(adjusted_gas, 400_000);
    }

    #[test]
    fn adjust_gas_small() {
        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier: 1.1,
            max_gas: 1_000_000,
            gas_amount: 400_000,
        });

        assert_eq!(adjusted_gas, 440_000);
    }

    #[test]
    fn adjust_gas_over_max() {
        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier: 3.0,
            max_gas: 1_000_000,
            gas_amount: 400_000,
        });

        assert_eq!(adjusted_gas, 1_000_000);
    }

    #[test]
    fn adjust_gas_overflow() {
        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier: 3.0,
            max_gas: u64::MAX,
            gas_amount: u64::MAX / 2,
        });

        assert_eq!(adjusted_gas, u64::MAX);
    }
}
