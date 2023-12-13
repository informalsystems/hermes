//! Result and execution types from results of RPC calls to the network.

use near_primitives::borsh;
use near_primitives::hash::CryptoHash;
use near_primitives::types::{AccountId, Balance, Gas};
use near_primitives::views::{
    CallResult, ExecutionOutcomeWithIdView, ExecutionStatusView, FinalExecutionOutcomeView,
    FinalExecutionStatus,
};
use tracing::warn;

use crate::chain::near::error::NearError;

/// Struct to hold a type we want to return along w/ the execution result view.
/// This view has extra info about the execution, such as gas usage and whether
/// the transaction failed to be processed on the chain.
pub struct CallExecution<T> {
    pub result: T,
    pub details: CallExecutionDetails,
}

impl<T> CallExecution<T> {
    pub fn unwrap(self) -> T {
        self.into_result().expect("unwrap into result failed")
    }

    pub fn into_result(self) -> anyhow::Result<T> {
        Into::<anyhow::Result<_>>::into(self)
    }

    /// Checks whether the transaction was successful. Returns true if
    /// the transaction has a status of FinalExecutionStatus::Success.
    pub fn is_success(&self) -> bool {
        self.details.is_success()
    }

    /// Checks whether the transaction has failed. Returns true if
    /// the transaction has a status of FinalExecutionStatus::Failure.
    pub fn is_failure(&self) -> bool {
        self.details.is_failure()
    }
}

impl<T> From<CallExecution<T>> for anyhow::Result<T> {
    fn from(value: CallExecution<T>) -> anyhow::Result<T> {
        match value.details.status {
            FinalExecutionStatus::SuccessValue(_) => Ok(value.result),
            FinalExecutionStatus::Failure(err) => Err(anyhow::anyhow!(err)),
            FinalExecutionStatus::NotStarted => Err(anyhow::anyhow!("Transaction not started.")),
            FinalExecutionStatus::Started => {
                Err(anyhow::anyhow!("Transaction still being processed."))
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
#[non_exhaustive]
pub struct CallExecutionDetails {
    /// Execution status. Contains the result in case of successful execution.
    pub(crate) status: FinalExecutionStatus,
    /// Total gas burnt by the call execution
    pub total_gas_burnt: Gas,

    pub(crate) transaction: ExecutionOutcome,
    pub(crate) receipts: Vec<ExecutionOutcome>,
}

impl CallExecutionDetails {
    /// Deserialize an instance of type `T` from bytes of JSON text sourced from the
    /// execution result of this call. This conversion can fail if the structure of
    /// the internal state does not meet up with [`serde::de::DeserializeOwned`]'s
    /// requirements.
    pub fn json<T: serde::de::DeserializeOwned>(&self) -> anyhow::Result<T> {
        let buf = self.raw_bytes()?;
        serde_json::from_slice(&buf).map_err(Into::into)
    }

    /// Deserialize an instance of type `T` from bytes sourced from the execution
    /// result. This conversion can fail if the structure of the internal state does
    /// not meet up with [`borsh::BorshDeserialize`]'s requirements.
    pub fn borsh<T: borsh::BorshDeserialize>(&self) -> anyhow::Result<T> {
        let buf = self.raw_bytes()?;
        borsh::BorshDeserialize::try_from_slice(&buf).map_err(Into::into)
    }

    /// Grab the underlying raw bytes returned from calling into a contract's function.
    /// If we want to deserialize these bytes into a rust datatype, use [`CallExecutionDetails::json`]
    /// or [`CallExecutionDetails::borsh`] instead.
    pub fn raw_bytes(&self) -> anyhow::Result<Vec<u8>> {
        let result = match self.status {
            FinalExecutionStatus::SuccessValue(ref val) => val,
            FinalExecutionStatus::Failure(ref err) => anyhow::bail!(err.clone()),
            FinalExecutionStatus::NotStarted => anyhow::bail!("Transaction not started."),
            FinalExecutionStatus::Started => anyhow::bail!("Transaction still being processed."),
        };
        base64::decode(result).map_err(Into::into)
    }

    /// Convert the execution details into a Result if its status is not a successful one.
    /// Useful for checking if the call was successful and forwarding the error upwards.
    fn try_into_result(self) -> anyhow::Result<Self> {
        match self.status {
            FinalExecutionStatus::Failure(ref err) => anyhow::bail!(err.clone()),
            FinalExecutionStatus::NotStarted => anyhow::bail!("Transaction not started."),
            FinalExecutionStatus::Started => anyhow::bail!("Transaction still being processed."),
            _ => (),
        };
        Ok(self)
    }

    pub fn from_outcome(outcome: FinalExecutionOutcomeView) -> anyhow::Result<Self> {
        Self::from(outcome).try_into_result()
    }

    /// Returns just the transaction outcome.
    pub fn outcome(&self) -> &ExecutionOutcome {
        &self.transaction
    }

    /// Grab all outcomes after the execution of the transaction. This includes outcomes
    /// from the transaction and all the receipts it generated.
    pub fn outcomes(&self) -> Vec<&ExecutionOutcome> {
        let mut outcomes = vec![&self.transaction];
        outcomes.extend(self.receipt_outcomes());
        outcomes
    }

    /// Grab all outcomes after the execution of the transaction. This includes outcomes
    /// only from receipts generated by this transaction.
    pub fn receipt_outcomes(&self) -> &[ExecutionOutcome] {
        &self.receipts
    }

    /// Grab all outcomes that did not succeed the execution of this transaction. This
    /// will also include the failures from receipts as well.
    pub fn failures(&self) -> Vec<&ExecutionOutcome> {
        let mut failures = Vec::new();
        if matches!(self.transaction.status, ExecutionStatusView::Failure(_)) {
            failures.push(&self.transaction);
        }
        failures.extend(self.receipt_failures());
        failures
    }

    /// Just like `failures`, grab only failed receipt outcomes.
    pub fn receipt_failures(&self) -> Vec<&ExecutionOutcome> {
        self.receipts
            .iter()
            .filter(|receipt| matches!(receipt.status, ExecutionStatusView::Failure(_)))
            .collect()
    }

    /// Checks whether the transaction was successful. Returns true if
    /// the transaction has a status of [`FinalExecutionStatus::SuccessValue`].
    pub fn is_success(&self) -> bool {
        matches!(self.status, FinalExecutionStatus::SuccessValue(_))
    }

    /// Checks whether the transaction has failed. Returns true if
    /// the transaction has a status of [`FinalExecutionStatus::Failure`].
    pub fn is_failure(&self) -> bool {
        matches!(self.status, FinalExecutionStatus::Failure(_))
    }

    /// Grab all logs from both the transaction and receipt outcomes.
    pub fn logs(&self) -> Vec<&str> {
        self.outcomes()
            .iter()
            .flat_map(|outcome| &outcome.logs)
            .map(String::as_str)
            .collect()
    }
}

impl From<FinalExecutionOutcomeView> for CallExecutionDetails {
    fn from(transaction_result: FinalExecutionOutcomeView) -> Self {
        CallExecutionDetails {
            status: transaction_result.status,
            total_gas_burnt: transaction_result.transaction_outcome.outcome.gas_burnt
                + transaction_result
                    .receipts_outcome
                    .iter()
                    .map(|t| t.outcome.gas_burnt)
                    .sum::<u64>(),
            transaction: transaction_result.transaction_outcome.into(),
            receipts: transaction_result
                .receipts_outcome
                .into_iter()
                .map(ExecutionOutcome::from)
                .collect(),
        }
    }
}

/// The result from a call into a View function. This contains the contents or
/// the results from the view function call itself. The consumer of this object
/// can choose how to deserialize its contents.
#[derive(PartialEq, Eq, Clone, Debug)]
#[non_exhaustive]
pub struct ViewResultDetails {
    /// Our result from our call into a view function.
    pub result: Vec<u8>,
    /// Logs generated from the view function.
    pub logs: Vec<String>,
}

impl ViewResultDetails {
    /// Deserialize an instance of type `T` from bytes of JSON text sourced from the
    /// execution result of this call. This conversion can fail if the structure of
    /// the internal state does not meet up with [`serde::de::DeserializeOwned`]'s
    /// requirements.
    pub fn json<T: serde::de::DeserializeOwned>(&self) -> Result<T, NearError> {
        let res = serde_json::from_slice(&self.result);
        if res.is_err() {
            warn!("serde deserilize error: {:?}", self.result);
        }

        res.map_err(NearError::serde_json_error)
    }

    /// Deserialize an instance of type `T` from bytes sourced from this view call's
    /// result. This conversion can fail if the structure of the internal state does
    /// not meet up with [`borsh::BorshDeserialize`]'s requirements.
    pub fn borsh<T: borsh::BorshDeserialize>(&self) -> anyhow::Result<T> {
        borsh::BorshDeserialize::try_from_slice(&self.result).map_err(Into::into)
    }
}

impl From<CallResult> for ViewResultDetails {
    fn from(result: CallResult) -> Self {
        ViewResultDetails {
            result: result.result,
            logs: result.logs,
        }
    }
}

/// Value type returned from an [`ExecutionOutcome`] or receipt result. This value
/// can be converted into the underlying Rust datatype, or directly grab the raw
/// bytes associated to the value.
#[derive(Debug)]
pub struct Value {
    pub repr: String,
}

impl Value {
    fn from_string(value: String) -> Self {
        Self { repr: value }
    }
}

/// The execution outcome of a transaction. This type contains all data relevant to
/// calling into a function, and getting the results back.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExecutionOutcome {
    pub block_hash: CryptoHash,
    /// Logs from this transaction or receipt.
    pub logs: Vec<String>,
    /// Receipt IDs generated by this transaction or receipt.
    pub receipt_ids: Vec<CryptoHash>,
    /// The amount of the gas burnt by the given transaction or receipt.
    pub gas_burnt: Gas,
    /// The amount of tokens burnt corresponding to the burnt gas amount.
    /// This value doesn't always equal to the `gas_burnt` multiplied by the gas price, because
    /// the prepaid gas price might be lower than the actual gas price and it creates a deficit.
    pub tokens_burnt: Balance,
    /// The id of the account on which the execution happens. For transaction this is signer_id,
    /// for receipt this is receiver_id.
    pub executor_id: AccountId,
    /// Execution status. Contains the result in case of successful execution.
    pub(crate) status: ExecutionStatusView,
}

impl ExecutionOutcome {
    /// Checks whether this execution outcome was a success. Returns true if a success value or
    /// receipt id is present.
    pub fn is_success(&self) -> bool {
        matches!(
            self.status,
            ExecutionStatusView::SuccessValue(_) | ExecutionStatusView::SuccessReceiptId(_)
        )
    }

    /// Checks whether this execution outcome was a failure. Returns true if it failed with
    /// an error or the execution state was unknown or pending.
    pub fn is_failure(&self) -> bool {
        matches!(
            self.status,
            ExecutionStatusView::Failure(_) | ExecutionStatusView::Unknown
        )
    }

    /// Converts this [`ExecutionOutcome`] into a Result type, where the failure is converted
    /// to an [`anyhow::Error`] object which can be downcasted later.
    pub fn into_result(self) -> anyhow::Result<ValueOrReceiptId> {
        match self.status {
            ExecutionStatusView::SuccessValue(value) => Ok(ValueOrReceiptId::Value(
                Value::from_string(base64::encode(value)),
            )),
            ExecutionStatusView::SuccessReceiptId(hash) => {
                Ok(ValueOrReceiptId::ReceiptId(CryptoHash(hash.0)))
            }
            ExecutionStatusView::Failure(err) => {
                Err(anyhow::anyhow!("Execution failed: {:?}", err))
            }
            ExecutionStatusView::Unknown => anyhow::bail!("Execution pending or unknown"),
        }
    }
}

/// Value or ReceiptId from a successful execution.
pub enum ValueOrReceiptId {
    /// The final action succeeded and returned some value or an empty vec encoded in base64.
    Value(Value),
    /// The final action of the receipt returned a promise or the signed transaction was converted
    /// to a receipt. Contains the receipt_id of the generated receipt.
    ReceiptId(CryptoHash),
}

impl From<ExecutionOutcomeWithIdView> for ExecutionOutcome {
    fn from(view: ExecutionOutcomeWithIdView) -> Self {
        ExecutionOutcome {
            block_hash: CryptoHash(view.block_hash.0),
            logs: view.outcome.logs,
            receipt_ids: view
                .outcome
                .receipt_ids
                .into_iter()
                .map(|c| CryptoHash(c.0))
                .collect(),
            gas_burnt: view.outcome.gas_burnt,
            tokens_burnt: view.outcome.tokens_burnt,
            executor_id: view.outcome.executor_id,
            status: view.outcome.status,
        }
    }
}
