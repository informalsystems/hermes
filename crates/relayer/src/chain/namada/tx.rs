use core::str::FromStr;
use core::time::Duration;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

use borsh::BorshDeserialize;
use ibc_proto::google::protobuf::Any;
use namada::ledger::args::{Tx as TxArgs, TxCustom};
use namada::ledger::masp::ShieldedContext;
use namada::ledger::parameters::storage as parameter_storage;
use namada::ledger::rpc::TxBroadcastData;
use namada::ledger::wallet::Wallet;
use namada::ledger::{signing, tx};
use namada::tendermint_rpc::endpoint::broadcast::tx_sync::Response as AbciPlusRpcResponse;
use namada::tendermint_rpc::HttpClient;
use namada::types::address::{Address, ImplicitAddress};
use namada::types::chain::ChainId;
use namada::types::error::Error as NamadaError;
use namada::types::key::RefTo;
use namada::types::transaction::{GasLimit, TxType};
use namada_apps::cli::api::CliClient;
use namada_apps::client::tx::CLIShieldedUtils;
use namada_apps::facade::tendermint_config::net::Address as TendermintAddress;
use namada_apps::wallet::CliWalletUtils;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::{IncludeProof, QueryHeight, QueryTxHash, QueryTxRequest};
use crate::error::Error;

use super::NamadaChain;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

impl NamadaChain {
    pub fn send_tx(&mut self, proto_msg: &Any) -> Result<Response, Error> {
        let mut ledger_address = TendermintAddress::from_str(&format!(
            "{}:{}",
            self.config.rpc_addr.host(),
            self.config.rpc_addr.port()
        ))
        .expect("invalid ledger address");
        let client = HttpClient::from_tendermint_address(&mut ledger_address);

        let mut tx_data = vec![];
        prost::Message::encode(proto_msg, &mut tx_data)
            .map_err(|e| Error::protobuf_encode(String::from("Message"), e))?;

        let chain_id = ChainId::from_str(self.config.id.as_str()).expect("invalid chain ID");

        let fee_token = self.config.gas_price.denom.clone();
        let fee_token = self
            .wallet
            .find_address(&fee_token)
            .ok_or_else(|| Error::namada_address_not_found(fee_token))?
            .clone();

        // fee
        let gas_limit_key = parameter_storage::get_fee_unshielding_gas_limit_key();
        let (value, _) = self.query(gas_limit_key, QueryHeight::Latest, IncludeProof::No)?;
        let gas_limit = GasLimit::try_from_slice(&value).map_err(Error::borsh_decode)?;

        // the wallet should exist because it's confirmed when the bootstrap
        let relayer_key_pair = self
            .wallet
            .find_key(&self.config.key_name, None)
            .expect("The relayer key should exist in the wallet");

        let relayer_addr = self
            .wallet
            .find_address(&self.config.key_name)
            .expect("The relayer doesn't exist in the wallet")
            .clone();

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
            wrapper_fee_payer: Some(relayer_key_pair.clone()),
            fee_amount: None,
            fee_token,
            fee_unshield: None,
            gas_limit,
            expiration: None,
            disposable_signing_key: false,
            chain_id: Some(chain_id),
            signing_keys: vec![relayer_key_pair],
            signatures: vec![],
            tx_reveal_code_path: PathBuf::from(tx::TX_REVEAL_PK),
            verification_key: None,
            password: None,
        };
        let args = TxCustom {
            tx: tx_args.clone(),
            code_path: Some(PathBuf::from(tx::TX_IBC_WASM)),
            data_path: Some(tx_data),
            serialized_tx: None,
            owner: relayer_addr.clone(),
        };

        let signing_data = self
            .rt
            .block_on(signing::aux_signing_data(
                &client,
                &mut self.wallet,
                &args.tx,
                &Some(args.owner.clone()),
                Some(args.owner.clone()),
            ))
            .map_err(Error::namada_tx)?;
        self.rt
            .block_on(Self::submit_reveal_aux(
                &mut self.wallet,
                &client,
                &tx_args,
                &relayer_addr,
            ))
            .map_err(Error::namada_tx)?;

        let mut shielded = ShieldedContext::<CLIShieldedUtils>::default();
        let (mut tx, _) = self
            .rt
            .block_on(tx::build_custom(
                &client,
                &mut self.wallet,
                &mut shielded,
                args.clone(),
                &signing_data.fee_payer,
            ))
            .map_err(Error::namada_tx)?;

        self.rt
            .block_on(signing::generate_test_vector(
                &client,
                &mut self.wallet,
                &tx,
            ))
            .map_err(Error::namada_tx)?;

        signing::sign_tx(&mut self.wallet, &args.tx, &mut tx, signing_data)
            .map_err(Error::namada_tx)?;

        let wrapper_hash = tx.header_hash().to_string();
        let decrypted_hash = tx
            .clone()
            .update_header(TxType::Raw)
            .header_hash()
            .to_string();
        let to_broadcast = TxBroadcastData::Live {
            tx,
            wrapper_hash,
            decrypted_hash: decrypted_hash.clone(),
        };
        let mut response = self
            .rt
            .block_on(tx::broadcast_tx(&self.rpc_client, &to_broadcast))
            .map_err(Error::namada_tx)?;
        // overwrite the tx decrypted hash for the tx query
        response.hash = decrypted_hash.parse().expect("invalid hash");
        Ok(into_response(response))
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

    // TODO: modify submit_reveal_aux() to call without Context in Namada
    async fn submit_reveal_aux(
        wallet: &mut Wallet<CliWalletUtils>,
        client: &HttpClient,
        args: &TxArgs,
        address: &Address,
    ) -> Result<(), NamadaError> {
        if let Address::Implicit(ImplicitAddress(pkh)) = address {
            let key = wallet
                .find_key_by_pkh(pkh, args.clone().password)
                .map_err(|e| NamadaError::Other(e.to_string()))?;
            let public_key = key.ref_to();

            if tx::is_reveal_pk_needed(client, address, args.force).await? {
                let signing_data =
                    signing::aux_signing_data(client, wallet, args, &None, None).await?;

                let mut shielded = ShieldedContext::<CLIShieldedUtils>::default();
                let (mut tx, _) = tx::build_reveal_pk(
                    client,
                    wallet,
                    &mut shielded,
                    args,
                    address,
                    &public_key,
                    &signing_data.fee_payer,
                )
                .await?;

                signing::generate_test_vector(client, wallet, &tx).await?;

                signing::sign_tx(wallet, args, &mut tx, signing_data)?;

                tx::process_tx(client, wallet, args, tx).await?;
            }
        }

        Ok(())
    }
}

/// Convert a broadcast response to one of the base Tendermint
fn into_response(resp: AbciPlusRpcResponse) -> Response {
    Response {
        code: u32::from(resp.code).into(),
        data: Vec::<u8>::from(resp.data).into(),
        log: resp.log.to_string(),
        hash: tendermint::Hash::from_str(&resp.hash.to_string()).unwrap(),
    }
}
