use core::str::FromStr;
use core::time::Duration;
use std::path::PathBuf;
use std::thread;
use std::time::Instant;

use borsh::BorshDeserialize;
use ibc_proto::google::protobuf::Any;
use namada::ledger::args::{InputAmount, Tx as TxArgs};
use namada::ledger::parameters::storage as parameter_storage;
use namada::ledger::rpc::TxBroadcastData;
use namada::ledger::signing::{sign_tx, TxSigningKey};
use namada::ledger::tx::{broadcast_tx, prepare_tx};
use namada::ledger::tx::{TX_IBC_WASM, TX_REVEAL_PK};
use namada::proto::{Code, Data, Tx};
use namada::tendermint_rpc::endpoint::broadcast::tx_sync::Response as AbciPlusRpcResponse;
use namada::types::chain::ChainId;
use namada::types::token::{Amount, DenominatedAmount};
use namada::types::transaction::{GasLimit, TxType};
use namada_apps::client::rpc::query_wasm_code_hash;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::chain::cosmos;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::{IncludeProof, QueryHeight, QueryTxHash, QueryTxRequest};
use crate::error::Error;

use super::NamadaChain;

pub const FEE_TOKEN: &str = "NAM";
const DEFAULT_MAX_GAS: u64 = 100_000;
const WAIT_BACKOFF: Duration = Duration::from_millis(300);

impl NamadaChain {
    pub fn send_tx(&mut self, proto_msg: &Any) -> Result<Response, Error> {
        let tx_code_hash = self
            .rt
            .block_on(query_wasm_code_hash(&self.rpc_client, TX_IBC_WASM))
            .expect("invalid wasm path");
        let mut tx_data = vec![];
        prost::Message::encode(proto_msg, &mut tx_data)
            .map_err(|e| Error::protobuf_encode(String::from("Message"), e))?;
        let chain_id = ChainId::from_str(self.config.id.as_str()).expect("invalid chain ID");

        let mut tx = Tx::new(TxType::Raw);
        tx.header.chain_id = chain_id.clone();
        tx.header.expiration = None;
        tx.set_data(Data::new(tx_data));
        tx.set_code(Code::from_hash(tx_code_hash));

        let fee_token = self
            .wallet
            .find_address(FEE_TOKEN)
            .ok_or_else(|| Error::namada_address_not_found(FEE_TOKEN.to_string()))?
            .clone();

        // fee
        let wrapper_tx_fees_key = parameter_storage::get_wrapper_tx_fees_key();
        let (value, _) = self.query(wrapper_tx_fees_key, QueryHeight::Latest, IncludeProof::No)?;
        let fee_amount = Amount::try_from_slice(&value[..]).map_err(Error::borsh_decode)?;
        let fee_amount = InputAmount::Unvalidated(DenominatedAmount::native(fee_amount));

        let gas_limit = Amount::native_whole(self.config.max_gas.unwrap_or(DEFAULT_MAX_GAS));
        let gas_limit = GasLimit::from(gas_limit);

        // the wallet should exist because it's confirmed when the bootstrap
        let relayer_addr = self
            .wallet
            .find_address(&self.config.key_name)
            .expect("The relayer doesn't exist in the wallet");

        let tx_args = TxArgs {
            dry_run: false,
            dump_tx: false,
            force: false,
            broadcast_only: true,
            ledger_address: (),
            initialized_account_alias: None,
            wallet_alias_force: false,
            fee_amount,
            fee_token,
            gas_limit,
            expiration: None,
            chain_id: Some(chain_id),
            signing_key: None,
            signer: Some(relayer_addr.clone()),
            tx_reveal_code_path: PathBuf::from(TX_REVEAL_PK),
            verification_key: None,
            password: None,
        };

        let (mut tx, _, pk) = self
            .rt
            .block_on(prepare_tx(
                &self.rpc_client,
                &mut self.wallet,
                &tx_args,
                tx,
                TxSigningKey::None,
                #[cfg(not(feature = "mainnet"))]
                false,
            ))
            .map_err(Error::namada_tx)?;

        self.rt
            .block_on(sign_tx(&mut self.wallet, &mut tx, &tx_args, &pk))
            .map_err(Error::namada_tx)?;

        let wrapper_hash = tx.header_hash().to_string();
        let decrypted_hash = tx
            .clone()
            .update_header(TxType::Raw)
            .header_hash()
            .to_string();
        let to_broadcast = TxBroadcastData::Wrapper {
            tx,
            wrapper_hash,
            decrypted_hash: decrypted_hash.clone(),
        };
        let mut response = self
            .rt
            .block_on(broadcast_tx(&self.rpc_client, &to_broadcast))
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
