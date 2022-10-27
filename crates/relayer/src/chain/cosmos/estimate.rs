use ibc_proto::cosmos::tx::v1beta1::{Fee, Tx};
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tonic::codegen::http::Uri;
use tracing::{debug, error, span, warn, Level};

use crate::chain::cosmos::encode::sign_tx;
use crate::chain::cosmos::gas::gas_amount_to_fee;
use crate::chain::cosmos::simulate::send_tx_simulate;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::gas::GasConfig;
use crate::config::types::Memo;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::util::pretty::PrettyFee;

pub async fn estimate_tx_fees(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Fee, Error> {
    let gas_config = &config.gas_config;

    debug!(
        "max fee, for use in tx simulation: {}",
        PrettyFee(&gas_config.max_fee)
    );

    let signed_tx = sign_tx(
        config,
        key_entry,
        account,
        tx_memo,
        messages,
        &gas_config.max_fee,
    )?;

    let tx = Tx {
        body: Some(signed_tx.body),
        auth_info: Some(signed_tx.auth_info),
        signatures: signed_tx.signatures,
    };

    let estimated_fee =
        estimate_fee_with_tx(gas_config, &config.grpc_address, &config.chain_id, tx).await?;

    Ok(estimated_fee)
}

async fn estimate_fee_with_tx(
    gas_config: &GasConfig,
    grpc_address: &Uri,
    chain_id: &ChainId,
    tx: Tx,
) -> Result<Fee, Error> {
    let estimated_gas = estimate_gas_with_tx(gas_config, grpc_address, tx).await?;

    if estimated_gas > gas_config.max_gas {
        debug!(
            id = %chain_id, estimated = ?estimated_gas, max = ?gas_config.max_gas,
            "send_tx: estimated gas is higher than max gas"
        );

        return Err(Error::tx_simulate_gas_estimate_exceeded(
            chain_id.clone(),
            estimated_gas,
            gas_config.max_gas,
        ));
    }

    let adjusted_fee = gas_amount_to_fee(gas_config, estimated_gas);

    debug!(
        id = %chain_id,
        "send_tx: using {} gas, fee {}",
        estimated_gas,
        PrettyFee(&adjusted_fee)
    );

    Ok(adjusted_fee)
}

/// Try to simulate the given tx in order to estimate how much gas will be needed to submit it.
///
/// It is possible that a batch of messages are fragmented by the caller (`send_msgs`) such that
/// they do not individually verify. For example for the following batch:
/// [`MsgUpdateClient`, `MsgRecvPacket`, ..., `MsgRecvPacket`]
///
/// If the batch is split in two TX-es, the second one will fail the simulation in `deliverTx` check.
/// In this case we use the `default_gas` param.
async fn estimate_gas_with_tx(
    gas_config: &GasConfig,
    grpc_address: &Uri,
    tx: Tx,
) -> Result<u64, Error> {
    let simulated_gas = send_tx_simulate(grpc_address, tx)
        .await
        .map(|sr| sr.gas_info);

    let _span = span!(Level::ERROR, "estimate_gas").entered();

    match simulated_gas {
        Ok(Some(gas_info)) => {
            debug!(
                "tx simulation successful, gas amount used: {:?}",
                gas_info.gas_used
            );

            Ok(gas_info.gas_used)
        }

        Ok(None) => {
            warn!(
                "tx simulation successful but no gas amount used was returned, falling back on default gas: {}",
                gas_config.default_gas
            );

            Ok(gas_config.default_gas)
        }

        // If there is a chance that the tx will be accepted once actually submitted, we fall
        // back on the default gas and will attempt to send it anyway.
        // See `can_recover_from_simulation_failure` for more info.
        Err(e) if can_recover_from_simulation_failure(&e) => {
            warn!(
                "failed to simulate tx, falling back on default gas because the error is potentially recoverable: {}",
                e.detail()
            );

            Ok(gas_config.default_gas)
        }

        Err(e) => {
            error!(
                "failed to simulate tx. propagating error to caller: {}",
                e.detail()
            );
            // Propagate the error, the retrying mechanism at caller may catch & retry.
            Err(e)
        }
    }
}

/// Determine whether the given error yielded by `tx_simulate`
/// can be recovered from by submitting the tx anyway.
fn can_recover_from_simulation_failure(e: &Error) -> bool {
    use crate::error::ErrorDetail::*;

    match e.detail() {
        GrpcStatus(detail) => {
            detail.is_client_state_height_too_low()
                || detail.is_account_sequence_mismatch_that_can_be_ignored()
                || detail.is_out_of_order_packet_sequence_error()
        }
        _ => false,
    }
}
