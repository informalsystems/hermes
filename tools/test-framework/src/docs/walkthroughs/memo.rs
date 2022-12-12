//! ## Memo Test
//!
//! This walkthrough illustrates an integration test that utilizes a non-empty
//! struct as test input. This test tests that the process of transferring
//! IBC messages preserves the `memo` field. For the purposes of this explanation,
//! the `memo` field is nothing more than a `String` field for carrying along
//! some arbitrary metadata as part of the transaction. 
//! 
//! The test in most of its entirety (some parts omitted for brevity) looks like this:
//! 
//! ```no_run
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
//! impl:TestOverrides for MemoTest {
//!     fn modify_relayer_config(&self, config: &mut Config) {
//!         for mut chain in config.chains.iter_mut() {
//!             chain.memo_prefix = self.memo.clone();
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
//! ```
