use std::time::Duration;

use tracing::{error_span, trace, warn};

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

        let balance = chain.query_balance(None, None).map_err(|e| {
            TaskError::Ignore(format!("failed to query balance for the account: {e}"))
        })?;

        match balance.amount.parse::<f64>() {
            Ok(amount) => {
                telemetry!(
                    wallet_balance,
                    &chain.id(),
                    &key.account(),
                    amount,
                    &balance.denom,
                );
                trace!(%amount, denom = %balance.denom, account = %key.account(), "wallet balance");
            }
            Err(e) => {
                warn!(
                    %balance.amount, denom = %balance.denom, account = %key.account(),
                    "unable to parse the wallet balance into a f64, the balance will therefore not be reported to telemetry. Reason: {}", e
                );
            }
        }
        Ok(Next::Continue)
    })
}

#[cfg(test)]
mod tests {
    use ibc_relayer_types::bigint::U256;

    // Test to confirm that any u256 fits in f64
    #[test]
    fn compare_f64_max_to_u256_max() {
        let f64_max = f64::MAX;
        let u256_max = U256::MAX;

        assert!(f64_max > u256_max.to_string().parse::<f64>().unwrap());
    }
}
