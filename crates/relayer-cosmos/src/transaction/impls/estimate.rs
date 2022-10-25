use async_trait::async_trait;
use core::fmt::Display;
use core::marker::PhantomData;
use ibc_proto::cosmos::tx::v1beta1::{Fee, Tx};
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::gas::gas_amount_to_fee;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tracing::{debug, error, warn};

use crate::transaction::impls::encode::CanSignTx;
use crate::transaction::impls::simulate::CanSendTxSimulate;
use crate::transaction::traits::fields::{HasChainId, HasDefaultGas, HasGasConfig, HasMaxGas};

#[async_trait]
pub trait CanEstimateTxFees: HasError {
    async fn estimate_tx_fees(&self, messages: &[Any]) -> Result<Fee, Self::Error>;
}

#[async_trait]
impl<Context> CanEstimateTxFees for Context
where
    Context: HasError + HasGasConfig + CanSignTx + CanEstimateTxGas,
{
    async fn estimate_tx_fees(&self, messages: &[Any]) -> Result<Fee, Self::Error> {
        let gas_config = self.gas_config();

        let signed_tx = self.sign_tx(messages, &gas_config.max_fee)?;

        let tx = Tx {
            body: Some(signed_tx.body),
            auth_info: Some(signed_tx.auth_info),
            signatures: signed_tx.signatures,
        };

        let estimated_gas = self.estimate_gas_with_tx(tx).await?;

        let adjusted_fee = gas_amount_to_fee(gas_config, estimated_gas);

        Ok(adjusted_fee)
    }
}

#[async_trait]
pub trait TxGasEstimator<Context: HasError> {
    async fn estimate_gas_with_tx(context: &Context, tx: Tx) -> Result<u64, Context::Error>;
}

#[async_trait]
pub trait CanEstimateTxGas: HasError {
    async fn estimate_gas_with_tx(&self, tx: Tx) -> Result<u64, Self::Error>;
}

pub struct BaseTxGasEstimator;

#[async_trait]
impl<Context> TxGasEstimator<Context> for BaseTxGasEstimator
where
    Context: HasError + HasDefaultGas + CanSendTxSimulate,
{
    async fn estimate_gas_with_tx(context: &Context, tx: Tx) -> Result<u64, Context::Error> {
        let default_gas = context.default_gas();

        let simulated_gas = context.send_tx_simulate(tx).await?
            .gas_info
            .map(|i| i.gas_used)
            .unwrap_or_else(|| {
                warn!(
                    "tx simulation successful but no gas amount used was returned, falling back on default gas: {}",
                    default_gas
                );
                default_gas
            });

        Ok(simulated_gas)
    }
}

pub struct RecoverableTxGasEstimator<InEstimator>(PhantomData<InEstimator>);

pub trait HasRecoverableErrorForSimulation: HasError {
    fn can_recover_from_simulation_failure(e: &Self::Error) -> bool;
}

#[async_trait]
impl<Context, InEstimator> TxGasEstimator<Context> for RecoverableTxGasEstimator<InEstimator>
where
    Context: HasRecoverableErrorForSimulation + HasDefaultGas,
    Context::Error: Display,
    InEstimator: TxGasEstimator<Context>,
{
    async fn estimate_gas_with_tx(context: &Context, tx: Tx) -> Result<u64, Context::Error> {
        let res = InEstimator::estimate_gas_with_tx(context, tx).await;

        match res {
            Ok(gas) => Ok(gas),
            Err(e) => {
                if Context::can_recover_from_simulation_failure(&e) {
                    warn!(
                        "failed to simulate tx, falling back on default gas because the error is potentially recoverable: {}",
                        e
                    );

                    let default_gas = context.default_gas();
                    Ok(default_gas)
                } else {
                    error!("failed to simulate tx. propagating error to caller: {}", e);
                    // Propagate the error, the retrying mechanism at caller may catch & retry.
                    Err(e)
                }
            }
        }
    }
}

pub struct MaxTxGasEstimator<InEstimator>(PhantomData<InEstimator>);

pub struct MaxGasExceededError {
    pub chain_id: ChainId,
    pub estimated_gas: u64,
    pub max_gas: u64,
}

#[async_trait]
impl<Context, InEstimator> TxGasEstimator<Context> for MaxTxGasEstimator<InEstimator>
where
    Context: HasRecoverableErrorForSimulation
        + InjectError<MaxGasExceededError>
        + HasMaxGas
        + HasChainId,
    Context::Error: Display,
    InEstimator: TxGasEstimator<Context>,
{
    async fn estimate_gas_with_tx(context: &Context, tx: Tx) -> Result<u64, Context::Error> {
        let estimated_gas = InEstimator::estimate_gas_with_tx(context, tx).await?;

        let max_gas = context.max_gas();
        let chain_id = context.chain_id();

        if estimated_gas > max_gas {
            debug!(
                id = %chain_id, estimated = ?estimated_gas, max = ?max_gas,
                "send_tx: estimated gas is higher than max gas"
            );

            return Err(Context::inject_error(MaxGasExceededError {
                chain_id: chain_id.clone(),
                estimated_gas,
                max_gas,
            }));
        }

        todo!()
    }
}
