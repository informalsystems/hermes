//! ## Memo Test
//!
//! This walkthrough illustrates an integration test that utilizes a non-empty
//! struct as test input. This test asserts that the process of transferring
//! IBC messages preserves the `memo` field. For the purposes of this explanation,
//! the `memo` field is nothing more than a `String` field for carrying along
//! some arbitrary metadata as part of the transaction.
//!
//! The test in most of its entirety (some parts omitted for brevity) looks like this:
//!
//! ```no_run
//! # use serde_json as json;
//! # use ibc_relayer::config::{types::Memo, Config};
//! # use ibc_relayer::config::ChainConfig;
//! # use ibc_test_framework::ibc::denom::derive_ibc_denom;
//! # use ibc_test_framework::prelude::*;
//! # use ibc_test_framework::util::random::{random_string, random_u128_range};
//!
//!
//! #[test]
//! fn test_memo() -> Result<(), Error> {
//!     let memo = Memo::new(random_string()).unwrap();
//!     let test = MemoTest { memo };
//!     run_binary_channel_test(&test)
//! }
//!
//! pub struct MemoTest {
//!     memo: Memo,
//! }
//!
//! impl TestOverrides for MemoTest {
//!     fn modify_relayer_config(&self, config: &mut Config) {
//!         for mut chain in config.chains.iter_mut() {
//!             match chain {
//!                 ChainConfig::CosmosSdk(chain_config) => {
//!                     chain_config.memo_prefix = self.memo.clone();
//!                 },
//!             }
//!         }
//!     }
//! }
//!
//! impl BinaryChannelTest for MemoTest {
//!     fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
//!         &self,
//!         _config: &TestConfig,
//!         _relayer: RelayerDriver,
//!         chains: ConnectedChains<ChainA, ChainB>,
//!         channel: ConnectedChannel<ChainA, ChainB>,
//!     ) -> Result<(), Error> {
//!         let denom_a = chains.node_a.denom();
//!
//!         let a_to_b_amount = random_u128_range(1000, 5000);
//!
//!         chains.node_a.chain_driver().ibc_transfer_token(
//!             &channel.port_a.as_ref(),
//!             &channel.channel_id_a.as_ref(),
//!             &chains.node_a.wallets().user1(),
//!             &chains.node_b.wallets().user1().address(),
//!             &denom_a.with_amount(a_to_b_amount).as_ref(),
//!         )?;
//!
//!         let denom_b = derive_ibc_denom(
//!             &channel.port_b.as_ref(),
//!             &channel.channel_id_b.as_ref(),
//!             &denom_a,
//!         )?;
//!
//!         chains.node_b.chain_driver().assert_eventual_wallet_amount(
//!             &chains.node_b.wallets().user1().address(),
//!             &denom_b.with_amount(a_to_b_amount).as_ref(),
//!         )?;
//!
//!         let tx_info = chains
//!             .node_b
//!             .chain_driver()
//!             .query_recipient_transactions(&chains.node_b.wallets().user1().address())?;
//!
//!         assert_tx_memo_equals(&tx_info, self.memo.as_str())?;
//!
//!         Ok(())
//!     }
//! }
//!
//! # fn assert_tx_memo_equals(tx_info: &json::Value, expected_memo: &str) -> Result<(), Error> {
//! #     debug!("comparing memo field from json value {}", tx_info);
//! #
//! #     let memo_field = &tx_info["txs"][0]["tx"]["body"]["memo"];
//! #
//! #     info!("memo field value: {}", memo_field);
//! #
//! #     let memo_str = memo_field
//! #         .as_str()
//! #         .ok_or_else(|| eyre!("expect memo string field to be present in JSON"))?;
//! #
//! #     assert_eq!(memo_str, expected_memo);
//! #
//! #     Ok(())
//! # }
//! ```
//!
//! This test runs initializes a `MemoTest` struct with a random string
//! in the `memo` field, then calls the `run_binary_channel_test` function
//! with it. The `TestOverrides` trait is implemented in order to set the
//! `memo_prefix` configuration value on the chains that are initialized
//! over the course of the test.
//!
//! At a high level, this test performs an IBC token transfer operation
//! from chain A to chain B. Once chain B has received the transaction
//! that chain A initialized, the test asserts that the value of the
//! memo string is indeed what we expected.
//!
//! The first two lines of the `run` function perform some necessary
//! setup for performing an IBC token transfer, namely fetching the
//! coin denomination of chain A as well as generating a random amount
//! of that denomination that will be sent to chain B. It then calls
//! the `ibc_token_transfer` function to generate a transaction with
//! this information, including the memo string that was generated
//! earlier, and sends it to chain B.
//!
//! Next, the `derive_ibc_denom` function is called in order to
//! calculate the appropriate amount of chain B's coin denomination
//! based on chain A's denomination and how much of that denomination
//! was sent over the transaction so that chain B can represent the
//! transferred value.
//!
//! The `assert_eventual_wallet_amount` function is then called on
//! chain B in order to confirm that the transaction was indeed
//! received by checking that chain B's wallet amount reflects the
//! expected updated value. The `query_recipient_transactions`
//! method is then called to fetch the memo value from the transaction
//! so that we can confirm that its value is indeed what we expect.
//!
//! You can find the file containing this test at `tools/integration-test/src/tests/memo.rs`.
