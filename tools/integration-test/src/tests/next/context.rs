use std::collections::HashMap;

use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::config::Config;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer_cosmos::contexts::full::builder::CosmosRelayBuilder;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_framework::full::all_for_one::builder::CanBuildAfoFullBiRelay;
use ibc_test_framework::error::{handle_generic_error, Error};
use ibc_test_framework::types::binary::chains::ConnectedChains;

pub fn build_cosmos_relay_context<ChainA, ChainB>(
    config: &Config,
    chains: &ConnectedChains<ChainA, ChainB>,
    packet_filter: PacketFilter,
) -> Result<impl AfoCosmosFullBiRelay, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let runtime = chains.node_a.value().chain_driver.runtime.clone();

    let AnySigningKeyPair::Secp256k1(key_a) = chains.handle_a().get_key()? else {
        return Err(Error::generic(eyre!("invalid key")))
    };

    let AnySigningKeyPair::Secp256k1(key_b) = chains.handle_b().get_key()? else {
        return Err(Error::generic(eyre!("invalid key")))
    };

    let key_map = HashMap::from([
        (chains.chain_id_a().cloned_value(), key_a),
        (chains.chain_id_b().cloned_value(), key_b),
    ]);

    let builder = CosmosRelayBuilder::new_wrapped(
        config.clone(),
        runtime.clone(),
        Default::default(),
        packet_filter,
        Default::default(),
        key_map,
    );

    let birelay = runtime
        .block_on(builder.build_afo_full_birelay(
            chains.chain_id_a().value(),
            chains.chain_id_b().value(),
            chains.client_id_a().value(),
            chains.client_id_b().value(),
        ))
        .map_err(handle_generic_error)?;

    Ok(birelay)
}
