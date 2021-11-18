/*!
    Re-export of common constructs that are used by test cases.
*/

pub use eyre::eyre;
pub use ibc_relayer::chain::handle::ChainHandle;
pub use ibc_relayer::config::Config;
pub use ibc_relayer::config::SharedConfig;
pub use ibc_relayer::foreign_client::ForeignClient;
pub use ibc_relayer::registry::SharedRegistry;
pub use tracing::{debug, error, info, warn};

pub use crate::chain::driver::{tagged::TaggedChainDriverExt, ChainDriver};
pub use crate::error::Error;
pub use crate::framework::overrides::TestOverrides;
pub use crate::types::binary::chains::ConnectedChains;
pub use crate::types::binary::channel::ConnectedChannel;
pub use crate::types::config::TestConfig;
pub use crate::types::single::node::{FullNode, TaggedFullNodeExt};
pub use crate::types::wallet::{
    TaggedTestWalletsExt, TaggedWallet, TestWallets, Wallet, WalletAddress, WalletId,
};
pub use crate::util::suspend::suspend;

pub use crate::framework::binary::channel::{
    run_binary_channel_test, run_two_way_binary_channel_test, BinaryChannelTest,
};

pub use crate::framework::binary::chain::{
    run_binary_chain_test, run_two_way_binary_chain_test, BinaryChainTest,
};

pub use crate::framework::binary::node::{run_binary_node_test, BinaryNodeTest};
