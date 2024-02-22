use std::{fmt::Debug, str::FromStr, time::Duration};

use serde::{de::DeserializeOwned, Deserialize, Serialize};

use ibc_relayer::{
    config::ChainConfig,
    rest::request::{Request, VersionInfo},
    supervisor::dump_state::SupervisorState,
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use ibc_relayer_rest::spawn;

enum TestResult {
    Success,
    WrongRequest(Request),
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", content = "result")]
#[serde(rename_all = "lowercase")]
enum JsonResult<R, E> {
    Success(R),
    Error(E),
}

async fn run_test<R, F>(port: u16, path: &str, expected: R, handler: F)
where
    R: Serialize + DeserializeOwned + Debug + PartialEq,
    F: FnOnce(Request) -> TestResult + Send + 'static,
{
    let (tx, rx) = crossbeam_channel::unbounded();

    let handle = spawn(("127.0.0.1", port), tx).unwrap();

    std::thread::spawn(move || match rx.recv() {
        Ok(r) => match handler(r) {
            TestResult::Success => (), // all good
            TestResult::WrongRequest(r) => panic!("got the wrong request: {r:?}"),
        },
        Err(e) => panic!("got an error: {e}"),
    });

    tokio::time::sleep(Duration::from_millis(200)).await;

    let response = reqwest::get(&format!("http://127.0.0.1:{port}{path}"))
        .await
        .unwrap()
        .json()
        .await
        .unwrap();
    // Workaround for serde_json deserialization failure
    // from_str/from_slice() failed for ChainConfig
    let response = serde_json::from_value::<R>(response).unwrap();

    assert_eq!(response, expected);

    drop(handle);
}

#[tokio::test]
async fn version() {
    let version = VersionInfo {
        name: "mock".to_string(),
        version: "0.0.0".to_string(),
    };

    let rest_api_version = VersionInfo {
        name: "ibc-relayer-rest".to_string(),
        version: "0.27.0".to_string(),
    };

    let result: JsonResult<_, ()> = JsonResult::Success(vec![version.clone(), rest_api_version]);

    run_test(19101, "/version", result, |req| match req {
        Request::Version { reply_to } => {
            reply_to.send(Ok(version)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    })
    .await
}

#[tokio::test]
async fn get_chains() {
    let chain_id = ChainId::from_str("mock-0").unwrap();
    let result: JsonResult<_, ()> = JsonResult::Success(vec![chain_id.clone()]);

    run_test(19102, "/chains", result, |req| match req {
        Request::GetChains { reply_to } => {
            reply_to.send(Ok(vec![chain_id])).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    })
    .await;
}

const MOCK_CHAIN_CONFIG: &str = r#"
id = 'mock-0'
type = 'CosmosSdk'
rpc_addr = 'http://127.0.0.1:26557'
grpc_addr = 'http://127.0.0.1:9091'
event_source = { mode = 'push', url = 'ws://127.0.0.1:26557/websocket', batch_delay = '500ms' }
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
max_gas = 3000000
gas_price = { price = 0.001, denom = 'stake' }
gas_multiplier = 1.1
max_msg_num = 30
max_tx_size = 2097152
clock_drift = '5s'
trusting_period = '14days'
trust_threshold = { numerator = '1', denominator = '3' }
"#;

#[tokio::test]
async fn get_chain() {
    let config: ChainConfig = toml::de::from_str(MOCK_CHAIN_CONFIG).unwrap();
    let result: JsonResult<_, ()> = JsonResult::Success(config.clone());

    run_test(19103, "/chain/mock-0", result, |req| match req {
        Request::GetChain { chain_id, reply_to } if chain_id.to_string().as_str() == "mock-0" => {
            reply_to.send(Ok(config)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    })
    .await;
}

#[tokio::test]
async fn state() {
    let state = SupervisorState::new(vec!["mock-0".parse().unwrap()], std::iter::empty());
    let result: JsonResult<_, ()> = JsonResult::Success(state.clone());

    run_test(19104, "/state", result, |req| match req {
        Request::State { reply_to } => {
            reply_to.send(Ok(state)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    })
    .await;
}
