use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_test_framework::prelude::{NaryChainTest, NaryConnectedChains, RelayerDriver, TestConfig, TestOverrides};
use ibc_proto::ibc::applications::query::v1::{MsgSubmitCrossChainQuery, QueryCrossChainQueryResult};
use prost;
use ibc_proto::ibc::core::client::v1::Height;
use ibc_test_framework::chain::exec::simple_exec;
use ibc_test_framework::error::Error;

struct Ics31Test;

impl TestOverrides for Ics31Test{}

trait ChainMessage {
    fn to_any(&self) -> Any;
}

impl ChainMessage for MsgSubmitCrossChainQuery {
    fn to_any(&self) -> Any {
        let mut encoded = Vec::new();
        prost::Message::encode(self, &mut encoded).unwrap();
        Any {
            type_url: "/ibc_query.v1.MsgSubmitCrossChainQuery".to_string(),
            value: encoded,
        }
    }
}

impl ChainMessage for QueryCrossChainQueryResult {
    fn to_any(&self) -> Any {
        let mut encoded = Vec::new();
        prost::Message::encode(self, &mut encoded).unwrap();
        Any {
            type_url: "/ibc_query.v1.QueryCrossChainQueryResult".to_string(),
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
        let msg_cross_chain_query_tx = MsgSubmitCrossChainQuery {
            path: "https://api.cosmos.silknodes.io/cosmos/bank/v1beta1/balances/cosmos18zfp9u7zxg3gel4r3txa2jqxme7jkw7dnvfjc8".to_string(),
            local_timeout_height: Some(Height {
                revision_number: 0,
                revision_height: 7000
            }),
            local_timeout_stamp: 1700000000,
            query_height: 12352258,
            chain_id: fullnode.clone().chain_driver.chain_id.to_string(),
            sender: wallet.clone().address.0,
        };

        fullnode.clone().chain_driver.send_tx(&wallet, vec![msg_cross_chain_query_tx.to_any()])?;

        let res = simple_exec(
            fullnode.clone().chain_driver.chain_id.as_str(),
            fullnode.clone().chain_driver.command_path.as_str(),
            &[
                "--node",
                fullnode.clone().chain_driver.rpc_listen_address().as_str(),
                "query",
                "ibc_query",
                "query-result",
                "query-0",
                "--chain-id",
                fullnode.clone().chain_driver.chain_id.as_str(),
            ],
        )?.stdout;

        println!("{}", res);

        Ok(())
    }
}


#[cfg(test)]
mod ics31 {
    use ibc_test_framework::error::Error;
    use ibc_test_framework::prelude::{run_self_connected_nary_chain_test};
    use crate::Ics31Test;

    #[test]
    fn test() -> Result<(), Error> {
        run_self_connected_nary_chain_test(&Ics31Test)
    }
}

fn main() {}
