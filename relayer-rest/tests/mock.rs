use std::str::FromStr;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::ChainConfig,
    rest::request::{Request, VersionInfo},
    supervisor::dump_state::SupervisorState,
};

use ibc_relayer_rest::{server::spawn, Config};

pub enum TestResult {
    Success,
    WrongRequest(Request),
}

fn run_test<F>(port: u16, path: &str, expected: &str, handler: F)
where
    F: FnOnce(Request) -> TestResult + Send + 'static,
{
    let config = Config {
        address: format!("127.0.0.1:{}", port),
    };

    let (handle, rx) = spawn(config);

    std::thread::spawn(move || match rx.recv() {
        Ok(r) => match handler(r) {
            TestResult::Success => (), // all good
            TestResult::WrongRequest(r) => panic!("got the wrong request: {:?}", r),
        },
        Err(e) => panic!("got an error: {}", e),
    });

    let response = ureq::get(&format!("http://127.0.0.1:{}{}", port, path))
        .call()
        .unwrap()
        .into_string()
        .unwrap();

    assert_eq!(response.as_str(), expected);

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
        version: "0.1.0".to_string(),
    };

    let versions = vec![version.clone(), rest_api_version];
    let expected = serde_json::to_string(&versions).unwrap();

    run_test(19101, "/", &expected, |req| match req {
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
    let result: Result<_, ()> = Ok(vec![chain_id.clone()]);
    let expected = serde_json::to_string(&result).unwrap();

    run_test(19102, "/chain", &expected, |req| match req {
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
gas_adjustment = 0.1
max_msg_num = 30
max_tx_size = 2097152
clock_drift = '5s'
trusting_period = '14days'
trust_threshold = { numerator = '1', denominator = '3' }
"#;

#[test]
fn get_chain() {
    let config: ChainConfig = toml::de::from_str(MOCK_CHAIN_CONFIG).unwrap();
    let result: Result<_, ()> = Ok(config.clone());
    let expected = serde_json::to_string(&result).unwrap();

    run_test(19103, "/chain/mock-0", &expected, |req| match req {
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
    let result: Result<_, ()> = Ok(state.clone());
    let expected = serde_json::to_string(&result).unwrap();

    run_test(19104, "/state", &expected, |req| match req {
        Request::State { reply_to } => {
            reply_to.send(Ok(state)).unwrap();
            TestResult::Success
        }
        req => TestResult::WrongRequest(req),
    });
}
