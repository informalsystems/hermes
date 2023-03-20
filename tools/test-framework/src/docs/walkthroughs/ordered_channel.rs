//! ## Ordered Channel Test
//!
//! This walkthrough illustrates the behavior or an integration test that makes
//! use of the `BinaryChannelTest` trait. This trait is used for test cases that
//! require two running full nodes connected via IBC channels with completed
//! handshakes. The relayer is initialized with chain handles and foreign clients
//! for interfacing with the running full nodes.
//!
//! The test itself checks that transactions sent over an ordered channel are
//! successfully relayed and received by the intended recipient, even when the
//! transaction was queued up to be sent before the relayer was started.
//!
//! The test in most of its entirety (some parts omitted for brevity) looks like this:
//!
//! ```no_run
//! # use ibc_test_framework::ibc::denom::derive_ibc_denom;
//! # use ibc_test_framework::prelude::*;
//! # use ibc_test_framework::util::random::random_u128_range;
//!
//! #[test]
//! fn test_ordered_channel() -> Result<(), Error> {
//!     run_binary_channel_test(&OrderedChannelTest)
//! }
//!
//! pub struct OrderedChannelTest;
//!
//! impl TestOverrides for OrderedChannelTest {
//!     fn modify_relayer_config(&self, config: &mut Config) {
//!         config.mode.packets.clear_on_start = false;
//!         config.mode.packets.clear_interval = 0;
//!     }
//!
//!     fn should_spawn_supervisor(&self) -> bool {
//!         false
//!     }
//!
//!     fn channel_order(&self) -> Order {
//!         Order::Ordered
//!     }
//! }
//!
//! impl BinaryChannelTest for OrderedChannelTest {
//!     fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
//!         &self,
//!         _config: &TestConfig,
//!         relayer: RelayerDriver,
//!         chains: ConnectedChains<ChainA, ChainB>,
//!         channel: ConnectedChannel<ChainA, ChainB>,
//!     ) -> Result<(), Error> {
//!         let denom_a = chains.node_a.denom();
//!
//!         let wallet_a = chains.node_a.wallets().user1().cloned();
//!         let wallet_b = chains.node_b.wallets().user1().cloned();
//!
//!         let balance_a = chains
//!             .node_a
//!             .chain_driver()
//!             .query_balance(&wallet_a.address(), &denom_a)?;
//!
//!         let amount1 = random_u128_range(1000, 5000);
//!
//!         info!(
//!             "Performing IBC transfer with amount {}, which should be relayed because it's an ordered channel",
//!             amount1
//!         );
//!
//!         chains.node_a.chain_driver().ibc_transfer_token(
//!             &channel.port_a.as_ref(),
//!             &channel.channel_id_a.as_ref(),
//!             &wallet_a.as_ref(),
//!             &wallet_b.address(),
//!             &denom_a.with_amount(amount1).as_ref(),
//!         )?;
//!
//!         sleep(Duration::from_secs(1));
//!
//!         relayer.with_supervisor(|| {
//!             sleep(Duration::from_secs(1));
//!
//!             let amount2 = random_u128_range(1000, 5000);
//!
//!             info!(
//!                 "Performing IBC transfer with amount {}, which should be relayed",
//!                 amount2
//!             );
//!
//!             chains.node_a.chain_driver().ibc_transfer_token(
//!                 &channel.port_a.as_ref(),
//!                 &channel.channel_id_a.as_ref(),
//!                 &wallet_a.as_ref(),
//!                 &wallet_b.address(),
//!                 &denom_a.with_amount(amount2).as_ref(),
//!             )?;
//!
//!             sleep(Duration::from_secs(1));
//!
//!             let denom_b = derive_ibc_denom(
//!                 &channel.port_b.as_ref(),
//!                 &channel.channel_id_b.as_ref(),
//!                 &denom_a,
//!             )?;
//!
//!             chains.node_a.chain_driver().assert_eventual_wallet_amount(
//!                 &wallet_a.address(),
//!                 &(balance_a - amount1 - amount2).as_ref(),
//!             )?;
//!
//!             chains.node_b.chain_driver().assert_eventual_wallet_amount(
//!                 &wallet_b.address(),
//!                 &denom_b.with_amount(amount1 + amount2).as_ref(),
//!             )?;
//!
//!             Ok(())
//!         })
//!     }
//! }
//! ```
//!
//! The test is run by calling the `run_binary_channel_test` function, passing it
//! a struct, `OrderdChannelTest`, upon which we implement the `TestOverrides`
//! trait in order to configure the behavior of the test. We define the
//! `should_spawn_supervisor` function to have it return false in order to not
//! automatically spawn a supervisor when the relayer is initialized; this is
//! necessary in order to queue up an IBC transaction such that it is pending
//! until the relayer is initialized, not before that. We also define the
//! `channel_order` function in order to set the initialized channels to the
//! ordered variant; by default, the test will initialize unordered channels.
//! Lastly, we define the `modify_relayer_config` function in order to toggle off
//! the `clear_on_start` option, as well as set the `clear_interval` option to 0.
//! Setting these options means the relayer itself will not relay any packets
//! that were pending before the relayer started; we want to ensure that the
//! behavior of the ordered channel is what is causing the pending transaction
//! to be relayed.
//!
//! The logic of the test itself is defined in the `run` function of the
//! `BinaryChannelTest` trait. In this function, we first set up the two wallets,
//! the sending wallet, `wallet_a`, which is associated with chain A, and the
//! receiving wallet, `wallet_b`, which is associated iwth chain B. The balance
//! of `wallet_a` is also saved. An IBC transfer is then made from chain A to chain
//! B. At this point, because no relayer has been initialized yet, the transaction
//! is in a pending state.
//!
//! At this point, a relayer instance is initialized. The first thing it does is
//! perform another IBC transfer from chain A to chain B. The test then asserts
//! that `wallet_a` was indeed debited appropriately, that both transactions went
//! through due to the behavior of the ordered channel. It then checks `wallet_b`'s
//! balance to ensure that it was credited with the expected amount. If the assertions
//! pass, we can confident that the ordered channel is indeed exhibiting the expected
//! behavior of picking up pending transactions that were queued up before the relayer
//! was started.
//!
//! You can find the file containing this test at `tools/integration-test/src/tests/ordered_channel.rs`.
