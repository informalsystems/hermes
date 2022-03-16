// use std::str::FromStr;

// use ibc::core::ics04_channel::Version;

// use crate::{
//     bootstrap::binary::{
//         channel::bootstrap_channel_with_connection, connection::bootstrap_connection,
//     },
//     prelude::*,
// };

// // #[test]
// // fn test_ica_filter() -> Result<(), Error> {
// //     run_binary_chain_test(&IcaFilterTest)
// // }

// pub struct IcaFilterTest;

// impl TestOverrides for IcaFilterTest {
//     // Use deterministic identifiers for clients, connections, and channels
//     fn modify_test_config(&self, config: &mut TestConfig) {
//         config.bootstrap_with_random_ids = false;
//     }

//     // Do not start supervisor at the beginning of test
//     fn spawn_supervisor(
//         &self,
//         _config: &SharedConfig,
//         _registry: &SharedRegistry<impl ChainHandle>,
//     ) -> Result<Option<SupervisorHandle>, Error> {
//         Ok(None)
//     }
// }

// impl BinaryChainTest for IcaFilterTest {
//     fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
//         &self,
//         _config: &TestConfig,
//         chains: ConnectedChains<ChainA, ChainB>,
//     ) -> Result<(), Error> {
//         let connection = bootstrap_connection(&chains.client_a_to_b, &chains.client_b_to_a, false)?;

//         dbg!(&connection);

//         let wallet_a = chains.node_a.wallets().user1().cloned();

//         dbg!(&wallet_a);

//         chains.node_a.chain_driver().register_interchain_account(
//             &wallet_a.address(),
//             &connection.connection_id_b.as_ref(),
//         )?;

//         let icahost = PortId::from_str("icahost").unwrap();
//         let icacontroller =
//             PortId::from_str(&format!("icacontroller-{}", wallet_a.address().value())).unwrap();

//         let port_a: TaggedPortIdRef<ChainA, ChainB> = DualTagged::new(&icahost);
//         let port_b: TaggedPortIdRef<ChainB, ChainA> = DualTagged::new(&icacontroller);

//         let version = Version::new(format!(
//             r#"""
//                 {{
//                   "version": "ics27-1",
//                   "controller_connection_id": {:?},
//                   "host_connection_id": {:?},
//                   "address": "",
//                   "encoding": "proto3",
//                   "tx_type": "sdk_multi_msg"
//                 }}
//             """#,
//             connection.connection_id_a.value().to_string(),
//             connection.connection_id_b.value().to_string(),
//         ));

//         dbg!(&version);

//         let channel = bootstrap_channel_with_connection(
//             &chains.handle_b,
//             &chains.handle_a,
//             connection,
//             &port_b,
//             &port_a,
//             Order::Ordered,
//             version,
//             false,
//         )?;

//         dbg!(&channel);

//         Ok(())
//     }
// }
