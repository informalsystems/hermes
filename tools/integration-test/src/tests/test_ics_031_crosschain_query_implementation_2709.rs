use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_test_framework::prelude::*;
use ibc_proto::ibc::applications::query::v1::{MsgSubmitCrossChainQuery, QueryCrossChainQueryResult};
use prost;
use ibc_proto::ibc::core::client::v1::Height;
use ibc_test_framework::chain::exec::simple_exec;
use ibc_test_framework::error::Error;
use std::time::Duration;
use base64;
use std::env;
use std::process::Command;

struct Ics31Test;

#[test]
fn test_ics_031_crosschain_query() -> Result<(), Error> {
    run_self_connected_nary_chain_test(&Ics31Test)
}

impl TestOverrides for Ics31Test{
    fn modify_test_config(&self, config: &mut TestConfig) {
        let arch = String::from_utf8_lossy(&Command::new("uname").arg("-a").output().unwrap().stdout).to_string();
        let base_dir = format!("{}/{}", env::current_dir().unwrap().to_string_lossy().to_string(), "chain-binaries");

        if arch.contains("GNU/Linux") {
            config.chain_command_path = format!("{}/{}", base_dir, "interchain-queriesd-amd64");
        } else if arch.contains("arm64") {
            config.chain_command_path = format!("{}/{}", base_dir, "interchain-queriesd-arm64");

        }
    }
}

trait ChainMessage {
    fn to_any(&self) -> Any;
}

impl ChainMessage for MsgSubmitCrossChainQuery {
    fn to_any(&self) -> Any {
        let mut encoded = Vec::new();
        prost::Message::encode(self, &mut encoded).unwrap();
        Any {
            type_url: "/ibc.applications.ibc_query.v1.MsgSubmitCrossChainQuery".to_string(),
            value: encoded,
        }
    }
}

impl ChainMessage for QueryCrossChainQueryResult {
    fn to_any(&self) -> Any {
        let mut encoded = Vec::new();
        prost::Message::encode(self, &mut encoded).unwrap();
        Any {
            type_url: "/ibc.applications.ibc_query.v1.QueryCrossChainQueryResult".to_string(),
            value: encoded,
        }
    }
}


impl NaryChainTest<1> for Ics31Test {
    fn run<Handle: ChainHandle>(
        &self,
        _config: &TestConfig,
        _relayer: RelayerDriver,
        chains: NaryConnectedChains<Handle, 1>,
    ) -> Result<(), Error> {
        let fullnode = chains.full_node_at::<0>().unwrap().0;
        let wallet = fullnode.clone().wallets.relayer;

        // Tx for submitting crosschain-query request
        let msg_cross_chain_query_tx = MsgSubmitCrossChainQuery {
            path: format!("{}/{}", fullnode.chain_driver.rpc_address(), "abci_info?"),
            local_timeout_height: Some(Height {
                revision_number: 0,
                revision_height: 10000
            }),
            local_timeout_stamp: 5000000000000000000,
            query_height: 1,
            chain_id: fullnode.clone().chain_driver.chain_id.to_string(),
            sender: wallet.clone().address.0,
        };

        fullnode.clone().chain_driver.send_tx(&wallet, vec![msg_cross_chain_query_tx.to_any()])?;

        // wait until the relayer fetches data from chain
        sleep(Duration::from_secs(5));

        let res = simple_exec(
            fullnode.clone().chain_driver.chain_id.as_str(),
            fullnode.clone().chain_driver.command_path.as_str(),
            &[
                "--node",
                fullnode.clone().chain_driver.rpc_listen_address().as_str(),
                "query",
                "ibc-query",
                "query-result",
                "query-0",
                "--chain-id",
                fullnode.clone().chain_driver.chain_id.as_str(),
            ],
        )?.stdout;

        // decode query result as base64 format
        let res_data_raw= res.split("\n").nth(0).unwrap();
        let data_base64 = res_data_raw.split(" ").nth(1).unwrap();
        let data = String::from_utf8_lossy(&base64::decode(data_base64).unwrap()).to_string();

        // to preserve the original format of query result didn't use info! macro
        println!("{}", data);

        Ok(())
    }
}



