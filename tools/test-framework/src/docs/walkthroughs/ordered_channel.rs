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
//! Like we've seen in other integration tests, the test is set up
