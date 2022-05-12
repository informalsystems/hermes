use std::time::Duration;

use tracing::{debug, error_span};

use crate::{
    chain::handle::ChainHandle,
    util::task::{spawn_background_task, Next, TaskHandle},
};

pub fn spawn_wallet_worker<Chain: ChainHandle>(chain: Chain) -> TaskHandle {
    use crate::{telemetry, util::task::TaskError};

    let span = error_span!("wallet", chain = %chain.id());

    spawn_background_task(span, Some(Duration::from_secs(5)), move || {
        let key = chain.get_key().map_err(|e| {
            TaskError::Fatal(format!("failed to get key in use by the relayer: {e}"))
        })?;

        let balance = chain.query_balance().map_err(|e| {
            TaskError::Ignore(format!("failed to query balance for the account: {e}"))
        })?;

        let amount = balance.amount.parse().map_err(|_| {
            TaskError::Ignore(format!(
                "failed to parse amount into u64: {}",
                balance.amount
            ))
        })?;

        debug!(%amount, denom = %balance.denom, account = %key.account, "wallet balance");

        telemetry!(
            wallet_balance,
            &chain.id(),
            &key.account,
            amount,
            &balance.denom,
        );

        Ok(Next::Continue)
    })
}
