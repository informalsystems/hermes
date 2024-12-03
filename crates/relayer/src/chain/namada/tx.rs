use core::str::FromStr;
use core::time::Duration;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

use ibc_proto::google::protobuf::Any;
use itertools::Itertools;
use namada_sdk::address::{Address, ImplicitAddress};
use namada_sdk::args::TxBuilder;
use namada_sdk::args::{Tx as TxArgs, TxCustom};
use namada_sdk::chain::ChainId;
use namada_sdk::io::NamadaIo;
use namada_sdk::tx::{prepare_tx, ProcessTxResponse};
use namada_sdk::{rpc, signing, tx, Namada};
use namada_tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tracing::{debug, debug_span, trace, warn};

use crate::chain::cosmos::gas::{adjust_estimated_gas, AdjustGas};
use crate::chain::cosmos::types::gas::max_gas_from_config_opt;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::cosmos::wait::all_tx_results_found;
use crate::chain::endpoint::ChainEndpoint;
use crate::error::{Error, ErrorDetail};

use super::error::{Error as NamadaError, ErrorDetail as NamadaErrorDetail};
use super::NamadaChain;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

impl NamadaChain {
    pub fn batch_txs(&mut self, msgs: &[Any]) -> Result<Response, Error> {
        if msgs.is_empty() {
            return Err(Error::send_tx("No message to be batched".to_string()));
        }

        let tx_args = self.make_tx_args()?;

        let relayer_key = self.get_key()?;
        let relayer_addr = relayer_key.address;

        let rt = self.rt.clone();
        rt.block_on(self.submit_reveal_aux(&tx_args, &relayer_addr))?;

        let args = TxCustom {
            tx: tx_args.clone(),
            code_path: Some(PathBuf::from(tx::TX_IBC_WASM)),
            data_path: None,
            serialized_tx: None,
            owner: Some(relayer_addr.clone()),
        };
        let mut txs = Vec::new();
        for msg in msgs {
            let (mut tx, signing_data) = rt
                .block_on(args.build(&self.ctx))
                .map_err(NamadaError::namada)?;
            self.set_tx_data(&mut tx, msg)?;
            txs.push((tx, signing_data.expect("signing_data should exist")));
        }
        let (mut tx, signing_data) = tx::build_batch(txs).map_err(NamadaError::namada)?;
        // This is fine, as only the relayers is signing the transactions
        let signing_data = signing_data.first().expect("SigningData should exist");

        // Estimate the fee with dry-run
        match self.estimate_fee(tx.clone(), &tx_args, signing_data) {
            // Set the estimated fee
            Ok(Some((fee_token, gas_limit, fee_amount))) => {
                self.prepare_tx_with_gas(&mut tx, &tx_args, &fee_token, gas_limit, fee_amount)?
            }
            Ok(None) => {
                // the default gas limit will be used
            }
            Err(err) => match err.detail() {
                ErrorDetail::Namada(namada_err) => {
                    match namada_err.source {
                        NamadaErrorDetail::DryRun(ref tx_results) => {
                            warn!("Simulation failed: {tx_results}");
                            // Return the failure response to avoid the actual request.
                            // The response will be converted to `TxSyncResult`.
                            let response = Response {
                                codespace: Default::default(),
                                // the code value isn't used, but it should be non-zero to
                                // recognize the transaction failed
                                code: 1.into(),
                                data: Default::default(),
                                log: format!("Simulation failed: Results {tx_results}"),
                                hash: Default::default(),
                            };
                            return Ok(response);
                        }
                        _ => return Err(err),
                    }
                }
                _ => return Err(err),
            },
        }

        rt.block_on(self.ctx.sign(
            &mut tx,
            &tx_args,
            signing_data.clone(),
            signing::default_sign,
            (),
        ))
        .map_err(NamadaError::namada)?;

        let tx_header_hash = tx.header_hash().to_string();
        let response = rt
            .block_on(self.ctx.submit(tx, &tx_args))
            .map_err(NamadaError::namada)?;

        match response {
            tx::ProcessTxResponse::Broadcast(mut response) => {
                // overwrite the tx decrypted hash for the tx query
                response.hash = tx_header_hash.parse().expect("invalid hash");
                Ok(response)
            }
            _ => unreachable!("The response type was unexpected"),
        }
    }

    fn make_tx_args(&mut self) -> Result<TxArgs, Error> {
        let chain_id = ChainId::from_str(self.config.id.as_str()).expect("invalid chain ID");

        let namada_key = self.get_key()?;
        let relayer_public_key = namada_key.secret_key.to_public();

        let tx_args = self.ctx.tx_builder();
        let tx_args = tx_args.chain_id(chain_id);
        let tx_args = tx_args.signing_keys(vec![relayer_public_key]);
        // Confirm the transaction later
        let mut tx_args = tx_args.broadcast_only(true);

        let memo = self
            .config
            .memo_overwrite
            .as_ref()
            .unwrap_or(&self.config.memo_prefix);
        let memo = if !memo.as_str().is_empty() {
            Some(memo.as_str().to_string().as_bytes().to_vec())
        } else {
            None
        };
        tx_args.memo = memo;

        Ok(tx_args)
    }

    fn set_tx_data(&self, tx: &mut tx::Tx, proto_msg: &Any) -> Result<(), Error> {
        let mut tx_data = vec![];
        prost::Message::encode(proto_msg, &mut tx_data)
            .map_err(|e| Error::protobuf_encode(String::from("Encoding the message failed"), e))?;
        tx.add_serialized_data(tx_data);
        Ok(())
    }

    fn estimate_fee(
        &self,
        mut tx: tx::Tx,
        args: &TxArgs,
        signing_data: &signing::SigningTxData,
    ) -> Result<Option<(Address, u64, f64)>, Error> {
        let chain_id = self.config.id.clone();
        let fee_token_str = self.config.gas_price.denom.clone();
        let fee_token = Address::from_str(&fee_token_str)
            .map_err(|_| NamadaError::address_decode(fee_token_str.clone()))?;
        let gas_price = self.config.gas_price.price;

        let max_block_gas_key = namada_sdk::parameters::storage::get_max_block_gas_key();
        let max_block_gas: u64 = self
            .rt
            .block_on(rpc::query_storage_value(
                self.ctx.client(),
                &max_block_gas_key,
            ))
            .map_err(NamadaError::namada)?;
        let max_gas = max_gas_from_config_opt(&self.config).unwrap_or(max_block_gas);

        let args = args.clone().dry_run_wrapper(true);
        // Set the max gas to the gas limit for the simulation
        self.prepare_tx_with_gas(&mut tx, &args, &fee_token, max_block_gas, gas_price)?;

        self.rt
            .block_on(self.ctx.sign(
                &mut tx,
                &args,
                signing_data.clone(),
                signing::default_sign,
                (),
            ))
            .map_err(NamadaError::namada)?;

        let response = match self.rt.block_on(self.ctx.submit(tx, &args)) {
            Ok(resp) => resp,
            Err(e) => {
                warn!(
                    id = %chain_id,
                    "send_tx: gas estimation failed, using the default gas limit. Error: {}",
                    e
                );
                return Ok(None);
            }
        };

        let estimated_gas = match response {
            ProcessTxResponse::DryRun(result) => {
                if result
                    .0
                    .iter()
                    .all(|(_, r)| matches!(&r, Ok(result) if result.is_accepted()))
                {
                    result.1.into()
                } else {
                    // All or some of requests will fail
                    return Err(NamadaError::dry_run(result.0).into());
                }
            }
            _ => unreachable!("Unexpected response"),
        };
        if estimated_gas > max_gas {
            debug!(
                id = %chain_id, estimated = ?estimated_gas, max_gas,
                "send_tx: estimated gas is higher than max gas"
            );

            return Err(Error::tx_simulate_gas_estimate_exceeded(
                chain_id,
                estimated_gas,
                max_gas,
            ));
        }

        let gas_multiplier = self.config.gas_multiplier.unwrap_or_default().to_f64();

        let adjusted_gas = adjust_estimated_gas(AdjustGas {
            gas_multiplier,
            max_gas,
            gas_amount: estimated_gas,
        });

        debug!(
            id = %chain_id,
            "send_tx: using {} gas, gas_price {:?}",
            estimated_gas,
            gas_price,
        );

        Ok(Some((fee_token, adjusted_gas, gas_price)))
    }

    fn prepare_tx_with_gas(
        &self,
        tx: &mut tx::Tx,
        args: &TxArgs,
        fee_token: &Address,
        gas_limit: u64,
        fee_amount: f64,
    ) -> Result<(), Error> {
        let relayer_key = self.get_key()?;
        let relayer_public_key = relayer_key.secret_key.to_public();

        let args = args
            .clone()
            .fee_token(fee_token.clone())
            .gas_limit(gas_limit.into())
            .fee_amount(
                fee_amount
                    .to_string()
                    .parse()
                    .expect("Fee should be parsable"),
            );
        let fee_amount = self
            .rt
            .block_on(signing::validate_fee(&self.ctx, &args))
            .map_err(NamadaError::namada)?;
        self.rt
            .block_on(prepare_tx(&args, tx, fee_amount, relayer_public_key))
            .map_err(NamadaError::namada)?;

        Ok(())
    }

    pub fn wait_for_block_commits(
        &self,
        tx_sync_results: &mut [TxSyncResult],
    ) -> Result<(), Error> {
        if all_tx_results_found(tx_sync_results) {
            return Ok(());
        }

        let chain_id = &self.id();
        crate::time!(
            "wait_for_block_commits",
            {
                "src_chain": chain_id,
            }
        );
        let _span = debug_span!("wait_for_block_commits", id = %chain_id).entered();

        let start_time = Instant::now();

        let hashes = tx_sync_results
            .iter()
            .map(|res| res.response.hash.to_string())
            .join(", ");

        debug!("waiting for commit of tx hashes(s) {}", hashes);

        loop {
            let elapsed = start_time.elapsed();

            if all_tx_results_found(tx_sync_results) {
                trace!(
                    "retrieved {} tx results after {} ms",
                    tx_sync_results.len(),
                    elapsed.as_millis(),
                );

                return Ok(());
            } else if elapsed > self.config.rpc_timeout {
                debug!("timed out after {} ms", elapsed.as_millis());
                return Err(Error::tx_no_confirmation());
            } else {
                thread::sleep(WAIT_BACKOFF);

                for tx_sync_result in tx_sync_results.iter_mut() {
                    if let Err(e) = self.update_tx_sync_result(tx_sync_result) {
                        debug!("update_tx_sync_result failed. It will be retried: {e}");
                    }
                }
            }
        }
    }

    fn update_tx_sync_result(&self, tx_sync_result: &mut TxSyncResult) -> Result<(), Error> {
        if let TxStatus::Pending { .. } = tx_sync_result.status {
            let tm_hash = namada_tendermint::Hash::from_bytes(
                namada_tendermint::hash::Algorithm::Sha256,
                tx_sync_result.response.hash.as_bytes(),
            )
            .expect("tendermint hash should be converted");
            // If the transaction failed, query_txs returns the IbcEvent::ChainError,
            // so that we don't attempt to resolve the transaction later on.
            let events = self.query_tx_events(&tm_hash)?;
            // If we get events back, progress was made, so we replace the events
            // with the new ones. in both cases we will check in the next iteration
            // whether or not the transaction was fully committed.
            if !events.is_empty() {
                tx_sync_result.events = events;
                tx_sync_result.status = TxStatus::ReceivedResponse;
            }
        }
        Ok(())
    }

    async fn submit_reveal_aux(&mut self, args: &TxArgs, address: &Address) -> Result<(), Error> {
        if let Address::Implicit(ImplicitAddress(pkh)) = address {
            let public_key = self
                .ctx
                .wallet()
                .await
                .find_public_key(pkh.to_string())
                .map_err(|e| NamadaError::namada(namada_sdk::error::Error::Other(e.to_string())))?;

            if tx::is_reveal_pk_needed(self.ctx.client(), address)
                .await
                .map_err(NamadaError::namada)?
            {
                let (mut tx, signing_data) = tx::build_reveal_pk(&self.ctx, args, &public_key)
                    .await
                    .map_err(NamadaError::namada)?;
                self.ctx
                    .sign(&mut tx, args, signing_data, signing::default_sign, ())
                    .await
                    .map_err(NamadaError::namada)?;
                self.ctx
                    .submit(tx, args)
                    .await
                    .map_err(NamadaError::namada)?;
            }
        }
        Ok(())
    }
}
