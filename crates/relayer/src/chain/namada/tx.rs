use core::str::FromStr;
use core::time::Duration;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

use ibc_proto::google::protobuf::Any;
use namada_parameters::storage as parameter_storage;
use namada_sdk::args::{Tx as TxArgs, TxCustom};
use namada_sdk::borsh::BorshDeserialize;
use namada_sdk::tx::data::GasLimit;
use namada_sdk::types::address::{Address, ImplicitAddress};
use namada_sdk::types::chain::ChainId;
use namada_sdk::{signing, tx, Namada};
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::{IncludeProof, QueryHeight, QueryTxHash, QueryTxRequest};
use crate::error::Error;

use super::error::Error as NamadaError;
use super::NamadaChain;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

impl NamadaChain {
    pub fn send_tx(&mut self, proto_msg: &Any) -> Result<Response, Error> {
        let mut tx_data = vec![];
        prost::Message::encode(proto_msg, &mut tx_data)
            .map_err(|e| Error::protobuf_encode(String::from("Message"), e))?;

        let chain_id = ChainId::from_str(self.config.id.as_str()).expect("invalid chain ID");

        let fee_token = &self.config.gas_price.denom;
        let fee_token = Address::decode(fee_token)
            .map_err(|_| NamadaError::address_decode(fee_token.to_string()))?;

        // fee
        let gas_limit_key = parameter_storage::get_fee_unshielding_gas_limit_key();
        let (value, _) = self.query(gas_limit_key, QueryHeight::Latest, IncludeProof::No)?;
        let gas_limit = GasLimit::try_from_slice(&value).map_err(NamadaError::borsh_decode)?;

        let namada_key = self.get_key()?;
        let relayer_public_key = namada_key.secret_key.to_public();
        let relayer_addr = namada_key.address;

        let memo = if !self.config().memo_prefix.as_str().is_empty() {
            Some(
                self.config()
                    .memo_prefix
                    .as_str()
                    .to_string()
                    .as_bytes()
                    .to_vec(),
            )
        } else {
            None
        };
        let tx_args = TxArgs {
            dry_run: false,
            dry_run_wrapper: false,
            dump_tx: false,
            force: false,
            output_folder: None,
            broadcast_only: true,
            ledger_address: (),
            initialized_account_alias: None,
            wallet_alias_force: false,
            wrapper_fee_payer: Some(relayer_public_key.clone()),
            fee_amount: None,
            fee_token,
            fee_unshield: None,
            gas_limit,
            expiration: None,
            disposable_signing_key: false,
            chain_id: Some(chain_id),
            signing_keys: vec![relayer_public_key],
            signatures: vec![],
            tx_reveal_code_path: PathBuf::from(tx::TX_REVEAL_PK),
            password: None,
            memo,
            use_device: false,
        };
        let rt = self.rt.clone();
        rt.block_on(self.submit_reveal_aux(&tx_args, &relayer_addr))?;

        let args = TxCustom {
            tx: tx_args.clone(),
            code_path: Some(PathBuf::from(tx::TX_IBC_WASM)),
            data_path: Some(tx_data),
            serialized_tx: None,
            owner: relayer_addr.clone(),
        };
        let (mut tx, signing_data) = rt
            .block_on(args.build(&self.ctx))
            .map_err(NamadaError::namada)?;
        rt.block_on(
            self.ctx
                .sign(&mut tx, &args.tx, signing_data, signing::default_sign, ()),
        )
        .map_err(NamadaError::namada)?;
        let decrypted_hash = tx.raw_header_hash().to_string();
        let response = rt
            .block_on(self.ctx.submit(tx, &args.tx))
            .map_err(NamadaError::namada)?;

        match response {
            tx::ProcessTxResponse::Broadcast(mut response) => {
                // overwrite the tx decrypted hash for the tx query
                response.hash = decrypted_hash.parse().expect("invalid hash");
                Ok(response)
            }
            _ => unreachable!("The response type was unexpected"),
        }
    }

    pub fn wait_for_block_commits(
        &self,
        tx_sync_results: &mut [TxSyncResult],
    ) -> Result<(), Error> {
        let start_time = Instant::now();
        loop {
            if cosmos::wait::all_tx_results_found(tx_sync_results) {
                return Ok(());
            }

            let elapsed = start_time.elapsed();
            if elapsed > self.config.rpc_timeout {
                return Err(Error::tx_no_confirmation());
            }

            thread::sleep(WAIT_BACKOFF);

            for TxSyncResult {
                response,
                events,
                status,
            } in tx_sync_results.iter_mut()
            {
                if let TxStatus::Pending { message_count: _ } = status {
                    // If the transaction failed, query_txs returns the IbcEvent::ChainError,
                    // so that we don't attempt to resolve the transaction later on.
                    if let Ok(events_per_tx) =
                        self.query_txs(QueryTxRequest::Transaction(QueryTxHash(response.hash)))
                    {
                        // If we get events back, progress was made, so we replace the events
                        // with the new ones. in both cases we will check in the next iteration
                        // whether or not the transaction was fully committed.
                        if !events_per_tx.is_empty() {
                            *events = events_per_tx;
                            *status = TxStatus::ReceivedResponse;
                        }
                    }
                }
            }
        }
    }

    async fn submit_reveal_aux(&mut self, args: &TxArgs, address: &Address) -> Result<(), Error> {
        if let Address::Implicit(ImplicitAddress(pkh)) = address {
            let public_key = self
                .ctx
                .wallet()
                .await
                .find_public_key(pkh.to_string())
                .map_err(|e| NamadaError::namada(namada_sdk::error::Error::Other(e.to_string())))?;

            if tx::is_reveal_pk_needed(self.ctx.client(), address, args.force)
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
