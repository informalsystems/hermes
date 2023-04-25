#[cfg(feature = "next")]
use {
    crate::framework::binary::next::TestContextV2, crate::prelude::handle_generic_error,
    ibc_relayer::keyring::Secp256k1KeyPair,
    ibc_relayer_all_in_one::extra::all_for_one::builder::CanBuildAfoFullBiRelay,
    ibc_relayer_cosmos::contexts::full::builder::CosmosRelayBuilder,
    ibc_relayer_types::core::ics24_host::identifier::ChainId, std::collections::HashMap,
    std::sync::Arc, tokio::runtime::Runtime as TokioRuntime,
};

#[cfg(not(feature = "next"))]
use crate::framework::binary::next::TestContextV1;

use crate::framework::next::chain::{
    CanShutdown, CanSpawnRelayer, CanWaitForAck, HasContextId, HasTestConfig, HasTwoChains,
    HasTwoChannels, HasTwoNodes,
};
use crate::prelude::*;

pub fn build_test_context<ChainA: ChainHandle, ChainB: ChainHandle>(
    config: &TestConfig,
    relayer: RelayerDriver,
    chains: ConnectedChains<ChainA, ChainB>,
    channels: ConnectedChannel<ChainA, ChainB>,
) -> Result<
    impl HasTwoChains
        + HasTwoChannels
        + HasTwoNodes
        + HasTestConfig
        + CanSpawnRelayer
        + HasContextId
        + CanWaitForAck
        + CanShutdown,
    Error,
> {
    cfg_if::cfg_if! {
        if #[cfg(feature = "next")] {

            let runtime = Arc::new(TokioRuntime::new().unwrap());

            // Build key map from existing keys in ChainHandle
            let mut key_map: HashMap<ChainId, Secp256k1KeyPair> = HashMap::new();
            let key_a = chains.handle_a().get_key().unwrap();
            if let ibc_relayer::keyring::AnySigningKeyPair::Secp256k1(secp256k1_a) = key_a {
                let chain_a_id = chains.handle_a().id();
                key_map.insert(chain_a_id, secp256k1_a);
            }
            let key_b = chains.handle_b().get_key().unwrap();
            if let ibc_relayer::keyring::AnySigningKeyPair::Secp256k1(secp256k1_b) = key_b {
                let chain_b_id = chains.handle_b().id();
                key_map.insert(chain_b_id, secp256k1_b);
            }

            let builder = CosmosRelayBuilder::new_wrapped(
                relayer.config,
                runtime.clone(),
                Default::default(),
                Default::default(),
                Default::default(),
                key_map,
            );

            let birelay = runtime.block_on(async {builder
                    .build_afo_full_birelay(
                        chains.chain_id_a().0,
                        chains.chain_id_b().0,
                        chains.client_id_a().0,
                        chains.client_id_b().0,
                    )
                    .await
                    .map_err(handle_generic_error)
                })?;

            let context_next = TestContextV2 {
                context_id: "relayer_next".to_owned(),
                config: config.clone(),
                relayer: birelay,
                chains,
                channel: channels,
            };

            Ok(context_next)
        } else {
            let context_current = TestContextV1 {
                context_id: "current_relayer".to_owned(),
                config: config.clone(),
                relayer,
                chains,
                channel: channels,
            };

            Ok(context_current)
        }
    }
}
