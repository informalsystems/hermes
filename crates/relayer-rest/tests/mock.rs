use std::str::FromStr;

use serde::{Deserialize, Serialize};

use ibc_relayer::{
    config::ChainConfig,
    rest::request::{Request, VersionInfo},
    supervisor::dump_state::SupervisorState,
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use ibc_relayer_rest::{server::spawn, Config};

enum TestResult {
    Success,
    WrongRequest(Request),
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "status", content = "result")]
#[serde(rename_all = "lowercase")]
enum JsonResult<R, E> {
    Success(R),
    Error(E),
}

fn run_test<R, F>(port: u16, path: &str, expected: R, handler: F)
where
    R: Serialize,
    F: FnOnce(Request) -> TestResult + Send + 'static,
{
    let config = Config::new("127.0.0.1".to_string(), port);

    let (handle, rx) = spawn(config);

    std::thread::spawn(move || match rx.recv() {
        Ok(r) => match handler(r) {
            TestResult::Success => (), // all good
            TestResult::WrongRequest(r) => panic!("got the wrong request: {r:?}"),
        },
        Err(e) => panic!("got an error: {e}"),
    });

    let response = ureq::get(&format!("http://127.0.0.1:{port}{path}"))
        .call()
        .unwrap()
        .into_string()
        .unwrap();

    let expected_json = serde_json::to_string(&expected).unwrap();
    assert_eq!(response, expected_json);

    handle.stop();
    handle.join().unwrap();
}

#[test]
fn version() {
    let version = VersionInfo {
        name: "mock".to_string(),
        version: "0.0.0".to_string(),
    };

    let rest_api_version = VersionInfo {
        name: "ibc-relayer-rest".to_string(),
        version: "0.23.0".to_string(),
    };

    let result = vec![version.clone(), rest_api_version];

    run_test(19101, "/version", result, |req| match req {
        Request::Version { reply_to } => {
            reply_to.send(Ok(version)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    })
}

#[test]
fn get_chains() {
    let chain_id = ChainId::from_str("mock-0").unwrap();
    let result: JsonResult<_, ()> = JsonResult::Success(vec![chain_id.clone()]);

    run_test(19102, "/chains", result, |req| match req {
        Request::GetChains { reply_to } => {
            reply_to.send(Ok(vec![chain_id])).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    });
}

const MOCK_CHAIN_CONFIG: &str = r#"
id = 'mock-0'
rpc_addr = 'http://127.0.0.1:26557'
grpc_addr = 'http://127.0.0.1:9091'
websocket_addr = 'ws://127.0.0.1:26557/websocket'
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

#[test]
fn get_chain() {
    let config: ChainConfig = toml::de::from_str(MOCK_CHAIN_CONFIG).unwrap();
    let result: JsonResult<_, ()> = JsonResult::Success(config.clone());

    run_test(19103, "/chain/mock-0", result, |req| match req {
        Request::GetChain { chain_id, reply_to } if chain_id.to_string().as_str() == "mock-0" => {
            reply_to.send(Ok(config)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    });
}

#[test]
fn state() {
    let state = SupervisorState::new(vec!["mock-0".parse().unwrap()], std::iter::empty());
    let result: JsonResult<_, ()> = JsonResult::Success(state.clone());

    run_test(19104, "/state", result, |req| match req {
        Request::State { reply_to } => {
            reply_to.send(Ok(state)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    });
}
