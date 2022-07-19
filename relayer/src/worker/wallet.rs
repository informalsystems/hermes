use std::{ops::Div, time::Duration};

use tracing::{error_span, trace};

use ibc::bigint::U256;

use crate::{
    chain::handle::ChainHandle,
    telemetry,
    util::task::{spawn_background_task, Next, TaskError, TaskHandle},
};

pub fn spawn_wallet_worker<Chain: ChainHandle>(chain: Chain) -> TaskHandle {
    let span = error_span!("wallet", chain = %chain.id());

    spawn_background_task(span, Some(Duration::from_secs(5)), move || {
        let key = chain.get_key().map_err(|e| {
            TaskError::Fatal(format!("failed to get key in use by the relayer: {e}"))
        })?;

        let balance = chain.query_balance(None).map_err(|e| {
            TaskError::Ignore(format!("failed to query balance for the account: {e}"))
        })?;

        let amount: U256 = U256::from_dec_str(&balance.amount).map_err(|_| {
            TaskError::Ignore(format!(
                "failed to parse amount into U256: {}",
                balance.amount
            ))
        })?;

        trace!(%amount, denom = %balance.denom, account = %key.account, "wallet balance");

        // The input domain `balance.amount` may exceed u64::MAX, which is the
        // largest value that can be reported via the Prometheus exporter.
        //
        // To work around this, we scale down the amount by 10^6 in an attempt
        // to fit it into a u64, effectively turning the denomination from
        // eg. uatom to atom. If the scaled down amount does not fit, we do
        // not report it.
        //
        // Example input that overflows, from sifchain-1: `349999631379421794336`.
        //
        let chain_config = chain.config().unwrap();
        if let Some(_scaled_amount) = scale_down(
            amount,
            chain_config.exponent_divider,
        ) {
            telemetry!(
                wallet_balance,
                &chain.id(),
                &key.account,
                _scaled_amount,
                &balance.denom,
            );
        } else {
            trace!(
                %amount, denom = %balance.denom, account = %key.account,
                "amount cannot be scaled down to fit into u64 and therefore won't be reported to telemetry"
            );
        }

        Ok(Next::Continue)
    })
}

/// Scale down the given amount by a factor of 10^exponent,
/// and return it as a `u64` if it fits.
fn scale_down(amount: U256, exponent: u32) -> Option<u64> {
    amount.div(10_u64.pow(exponent)).try_into().ok()
}

#[cfg(test)]
mod tests {
    use super::scale_down;
    use ibc::bigint::U256;

    #[test]
    fn example_input() {
        let u: U256 =
            U256::from_dec_str("349999631379421794336").expect("failed to parse into U256");

        let s = scale_down(u, 6);
        assert_eq!(s, Some(349999631379421_u64));
    }

    #[test]
    fn example_result_too_big() {
        let u: U256 =
            U256::from_dec_str("349999631379421794336").expect("failed to parse into U256");

        let s = scale_down(u, 0);
        assert!(s.is_none());
    }

    #[test]
    fn example_zero_exponent() {
        let expected = 3499996313794217_u64;
        let u: U256 = U256::from(expected);

        let s = scale_down(u, 0);
        assert_eq!(s, Some(expected));
    }
}
