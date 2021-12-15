/*!
   Test for verifying the solution in
   [#1542](https://github.com/informalsystems/ibc-rs/pull/1542)

   On running the test, the log should show messages like:

   ```text
   2021-11-05T14:12:09.633184Z  WARN ThreadId(30) [ibc-1] estimate_gas: failed to simulate tx, falling back on default gas because the error is potentially recoverable: gRPC call failed with status: status: InvalidArgument, message: "failed to execute message; message index: 0: acknowledge packet verification failed: packet acknowledgement verification failed: failed packet acknowledgement verification for client (07-tendermint-0): client state height < proof height ({0 243} < {0 554}): invalid height: invalid request", details: [], metadata: MetadataMap { headers: {"content-type": "application/grpc"} }
   2021-11-05T14:12:09.633290Z DEBUG ThreadId(30) [ibc-1] send_tx: using 900000000 gas, fee Fee { amount: "900000stake", gas_limit: 900000000 }
   2021-11-05T14:12:09.639044Z DEBUG ThreadId(30) [ibc-1] send_tx: broadcast_tx_sync: Response { code: Ok, data: Data([]), log: Log("[]"), hash: transaction::Hash(BA94AE4CA198F56E27B4A44DA5E508A2E2207E306F475E5285D873296D892170) }
   ```
*/

use core::time::Duration;
use ibc_relayer::config::{types::MaxMsgNum, Config};

use crate::prelude::*;
use crate::relayer::transfer::tx_raw_ft_transfer;

#[test]
fn test_simulation() -> Result<(), Error> {
    run_binary_channel_test(&SimulationTest)
}

const MAX_MSGS: usize = 5;

pub struct SimulationTest;

impl TestOverrides for SimulationTest {
    fn modify_relayer_config(&self, config: &mut Config) {
        for mut chain in config.chains.iter_mut() {
            chain.max_msg_num = MaxMsgNum(MAX_MSGS);
        }
    }
}

impl BinaryChannelTest for SimulationTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        tx_raw_ft_transfer(
            chains.handle_a(),
            chains.handle_b(),
            &channel,
            &chains.node_b.wallets().user1().address(),
            &chains.node_a.denom(),
            9999,
            1000,
            Duration::from_secs(0),
            MAX_MSGS,
        )?;

        crate::suspend()
    }
}
