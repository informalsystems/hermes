/// HTTP JSON-RPC 2.0 client for the `stellar-rpc` service.
///
/// stellar-rpc exposes a JSON-RPC 2.0 interface over HTTP POST. There is no gRPC and no
/// WebSocket subscription — all communication is synchronous request/response over HTTP.
///
/// Public endpoints:
/// - Testnet: `https://soroban-testnet.stellar.org`
/// - Mainnet: `https://mainnet.sorobanrpc.com`
/// - Local (quickstart): `http://127.0.0.1:8000/rpc`
use serde_derive::{Deserialize, Serialize};
use serde_json::Value;

use crate::chain::stellar::error::Error;

// ── JSON-RPC envelope ──────────────────────────────────────────────────────────

#[derive(Debug, Serialize)]
struct JsonRpcRequest<'a> {
    jsonrpc: &'a str,
    id: u64,
    method: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    params: Option<Value>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcResponse<T> {
    #[allow(dead_code)]
    id: Option<Value>,
    result: Option<T>,
    error: Option<JsonRpcError>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcError {
    code: i64,
    message: String,
}

// ── Response types ─────────────────────────────────────────────────────────────

/// Response from `getHealth`.
#[derive(Debug, Deserialize)]
pub struct HealthResponse {
    pub status: String,
}

/// Response from `getLatestLedger`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LatestLedgerResponse {
    /// Ledger sequence number (block height).
    pub sequence: u32,
    /// Hex-encoded hash of the ledger header.
    pub id: String,
    /// Protocol version.
    pub protocol_version: u32,
}

/// A single ledger entry from `getLedgers`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LedgerEntry {
    pub sequence: u32,
    pub ledger_close_time: u64,
    /// Base64-encoded XDR `LedgerHeader`.
    pub ledger_header_xdr: String,
    /// Base64-encoded XDR `LedgerCloseMeta` (contains scpInfo for consensus proof).
    pub ledger_metadata_xdr: Option<String>,
}

/// Response from `getLedgers`.
#[derive(Debug, Deserialize)]
pub struct LedgersResponse {
    pub ledgers: Vec<LedgerEntry>,
    pub cursor: Option<String>,
}

/// A single contract event from `getEvents`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ContractEvent {
    /// `C...` contract address that emitted this event.
    pub contract_id: Option<String>,
    /// Event type: `"contract"`, `"system"`, or `"diagnostic"`.
    pub r#type: String,
    /// Ledger sequence containing this event.
    pub ledger: u32,
    /// UNIX timestamp of the ledger close.
    pub ledger_close_time: u64,
    /// Base64-encoded XDR `SCVal[]` topic array.
    pub topic: Vec<String>,
    /// Base64-encoded XDR `SCVal` payload.
    pub value: String,
    /// Pagination cursor in `{Ledger,Tx,Op,Event}` TOID format.
    pub id: String,
    pub paging_token: String,
    /// Transaction hash that produced this event.
    pub tx_hash: String,
}

/// Response from `getEvents`.
#[derive(Debug, Deserialize)]
pub struct EventsResponse {
    pub events: Vec<ContractEvent>,
    pub cursor: Option<String>,
}

/// Response from `getTransaction`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionResponse {
    /// `"SUCCESS"`, `"FAILED"`, `"NOT_FOUND"`.
    pub status: String,
    pub ledger: Option<u32>,
    pub ledger_close_time: Option<u64>,
    /// Base64-encoded XDR `TransactionMeta` (contains `SorobanTransactionMeta.events`).
    pub result_meta_xdr: Option<String>,
    pub error_result_xdr: Option<String>,
}

/// Status returned immediately after `sendTransaction`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SendTransactionResponse {
    /// `"PENDING"`, `"DUPLICATE"`, `"TRY_AGAIN_LATER"`, `"ERROR"`.
    pub status: String,
    pub hash: Option<String>,
    pub error_result_xdr: Option<String>,
}

/// Resource fee estimate from `simulateTransaction`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SimulateTransactionResponse {
    /// Minimum resource fee in stroops.
    pub min_resource_fee: Option<String>,
    /// Base64-encoded XDR `SorobanTransactionData` (read/write footprint + resource limits).
    pub transaction_data: Option<String>,
    pub error: Option<String>,
    pub results: Option<Vec<SimulateResult>>,
}

#[derive(Debug, Deserialize)]
pub struct SimulateResult {
    pub xdr: String,
}

/// A single ledger entry returned by `getLedgerEntries`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LedgerEntryResult {
    /// Base64-encoded XDR `LedgerKey`.
    pub key: String,
    /// Base64-encoded XDR `LedgerEntryData`.
    pub xdr: String,
    pub last_modified_ledger_seq: Option<u32>,
    pub live_until_ledger_seq: Option<u32>,
}

/// Response from `getLedgerEntries`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LedgerEntriesResponse {
    pub entries: Option<Vec<LedgerEntryResult>>,
    pub latest_ledger: u32,
}

/// Response from `getNetwork`.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkResponse {
    /// Network passphrase (used to verify config and for tx signing).
    pub passphrase: String,
    pub protocol_version: Option<u32>,
    pub history_latest_ledger: Option<u32>,
}

// ── Client ─────────────────────────────────────────────────────────────────────

/// Async HTTP JSON-RPC 2.0 client for stellar-rpc.
pub struct StellarRpcClient {
    rpc_url: String,
    http: reqwest::Client,
}

impl StellarRpcClient {
    pub fn new(rpc_url: String) -> Self {
        Self {
            rpc_url,
            http: reqwest::Client::new(),
        }
    }

    async fn call<T: for<'de> serde::Deserialize<'de>>(
        &self,
        method: &str,
        params: Option<Value>,
    ) -> Result<T, Error> {
        let request = JsonRpcRequest {
            jsonrpc: "2.0",
            id: 1,
            method,
            params,
        };

        let response = self
            .http
            .post(&self.rpc_url)
            .json(&request)
            .send()
            .await
            .map_err(|e| Error::rpc_client(format!("{}: {}", method, e)))?;

        let body: JsonRpcResponse<T> = response
            .json()
            .await
            .map_err(|e| Error::rpc_client(format!("{} response parse: {}", method, e)))?;

        if let Some(err) = body.error {
            return Err(Error::rpc_client(format!(
                "{} error {}: {}",
                method, err.code, err.message
            )));
        }

        body.result
            .ok_or_else(|| Error::rpc_client(format!("{}: empty result", method)))
    }

    /// Check whether stellar-rpc is healthy.
    pub async fn get_health(&self) -> Result<HealthResponse, Error> {
        self.call("getHealth", None).await
    }

    /// Return the latest ledger sequence and hash.
    pub async fn get_latest_ledger(&self) -> Result<LatestLedgerResponse, Error> {
        self.call("getLatestLedger", None).await
    }

    /// Return a range of ledgers with headers and metadata.
    pub async fn get_ledgers(
        &self,
        start_ledger: u32,
        cursor: Option<&str>,
        limit: Option<u32>,
    ) -> Result<LedgersResponse, Error> {
        let params = serde_json::json!({
            "startLedger": start_ledger,
            "cursor": cursor,
            "limit": limit,
        });
        self.call("getLedgers", Some(params)).await
    }

    /// Return contract events within a ledger range, optionally filtered by contract and topics.
    pub async fn get_events(
        &self,
        start_ledger: u32,
        contract_id: &str,
        cursor: Option<&str>,
        limit: Option<u32>,
    ) -> Result<EventsResponse, Error> {
        let params = serde_json::json!({
            "startLedger": start_ledger,
            "filters": [{ "type": "contract", "contractIds": [contract_id] }],
            "cursor": cursor,
            "limit": limit,
        });
        self.call("getEvents", Some(params)).await
    }

    /// Poll for the result of a previously submitted transaction.
    pub async fn get_transaction(&self, hash: &str) -> Result<TransactionResponse, Error> {
        let params = serde_json::json!({ "hash": hash });
        self.call("getTransaction", Some(params)).await
    }

    /// Submit a base64-encoded `TransactionEnvelope` XDR.
    /// Returns immediately with `PENDING` / `ERROR` etc. — poll `get_transaction` for finality.
    pub async fn send_transaction(&self, transaction_xdr: &str) -> Result<SendTransactionResponse, Error> {
        let params = serde_json::json!({ "transaction": transaction_xdr });
        self.call("sendTransaction", Some(params)).await
    }

    /// Dry-run a transaction to obtain the `SorobanTransactionData` footprint and resource fee.
    /// Must be called before signing and submitting any `invokeHostFunction` transaction.
    pub async fn simulate_transaction(
        &self,
        transaction_xdr: &str,
    ) -> Result<SimulateTransactionResponse, Error> {
        let params = serde_json::json!({ "transaction": transaction_xdr });
        self.call("simulateTransaction", Some(params)).await
    }

    /// Read current on-chain state for the given base64-encoded XDR `LedgerKey` list.
    pub async fn get_ledger_entries(
        &self,
        keys: Vec<String>,
    ) -> Result<LedgerEntriesResponse, Error> {
        let params = serde_json::json!({ "keys": keys });
        self.call("getLedgerEntries", Some(params)).await
    }

    /// Fetch the network passphrase (used to verify config and compute transaction hashes).
    pub async fn get_network(&self) -> Result<NetworkResponse, Error> {
        self.call("getNetwork", None).await
    }
}
