use alloc::sync::Arc;
use std::collections::HashMap;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;
use tokio::task;

use eyre::eyre;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::config::Config;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer::spawn::spawn_chain_runtime;
use ibc_relayer_all_in_one::one_for_all::types::builder::OfaBuilderWrapper;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_components_extra::batch::types::config::BatchConfig;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use tokio::runtime::Runtime as TokioRuntime;

use crate::contexts::chain::CosmosChain;
use crate::contexts::relay::CosmosRelay;
use crate::types::batch::CosmosBatchSender;
use crate::types::error::{BaseError, Error};
use crate::types::telemetry::CosmosTelemetry;

pub struct CosmosBuilder {
    pub config: Config,
    pub packet_filter: PacketFilter,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub runtime: TokioRuntimeContext,
    pub batch_config: BatchConfig,
    pub key_map: HashMap<ChainId, Secp256k1KeyPair>,
}

impl CosmosBuilder {
    pub fn new(
        config: Config,
        runtime: Arc<TokioRuntime>,
        telemetry: CosmosTelemetry,
        packet_filter: PacketFilter,
        batch_config: BatchConfig,
        key_map: HashMap<ChainId, Secp256k1KeyPair>,
    ) -> Self {
        let telemetry = OfaTelemetryWrapper::new(telemetry);

        let runtime = TokioRuntimeContext::new(runtime);

        Self {
            config,
            packet_filter,
            telemetry,
            runtime,
            batch_config,
            key_map,
        }
    }

    pub fn new_wrapped(
        config: Config,
        runtime: Arc<TokioRuntime>,
        telemetry: CosmosTelemetry,
        packet_filter: PacketFilter,
        batch_config: BatchConfig,
        key_map: HashMap<ChainId, Secp256k1KeyPair>,
    ) -> OfaBuilderWrapper<Self> {
        OfaBuilderWrapper::new_with_homogenous_cache(Self::new(
            config,
            runtime,
            telemetry,
            packet_filter,
            batch_config,
            key_map,
        ))
    }

    pub async fn build_chain(
        &self,
        chain_id: &ChainId,
    ) -> Result<CosmosChain<BaseChainHandle>, Error> {
        let runtime = self.runtime.runtime.clone();

        let (handle, key, chain_config) = task::block_in_place(|| -> Result<_, Error> {
            let handle = spawn_chain_runtime::<BaseChainHandle>(&self.config, chain_id, runtime)
                .map_err(BaseError::spawn)?;

            let key = get_keypair(chain_id, &handle, &self.key_map)?;

            let chain_config = handle.config().map_err(BaseError::relayer)?;

            Ok((handle, key, chain_config))
        })?;

        let event_source_mode = chain_config.event_source.clone();

        let tx_config = TxConfig::try_from(&chain_config).map_err(BaseError::relayer)?;

        let mut rpc_client =
            HttpClient::new(tx_config.rpc_address.clone()).map_err(BaseError::tendermint_rpc)?;

        let status = rpc_client.status().await.unwrap();
        let compat_mode = CompatMode::from_version(status.node_info.version).unwrap();

        rpc_client.set_compat_mode(compat_mode);

        let context = CosmosChain::new(
            handle,
            tx_config,
            rpc_client,
            compat_mode,
            key,
            event_source_mode,
            self.runtime.clone(),
            self.telemetry.clone(),
        );

        Ok(context)
    }

    pub fn build_relay(
        &self,
        src_client_id: &ClientId,
        dst_client_id: &ClientId,
        src_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        dst_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        src_batch_sender: CosmosBatchSender,
        dst_batch_sender: CosmosBatchSender,
    ) -> Result<CosmosRelay<BaseChainHandle, BaseChainHandle>, Error> {
        let relay = CosmosRelay::new(
            self.runtime.clone(),
            src_chain,
            dst_chain,
            src_client_id.clone(),
            dst_client_id.clone(),
            self.packet_filter.clone(),
            src_batch_sender,
            dst_batch_sender,
        );

        Ok(relay)
    }
}

pub fn get_keypair(
    chain_id: &ChainId,
    handle: &BaseChainHandle,
    key_map: &HashMap<ChainId, Secp256k1KeyPair>,
) -> Result<Secp256k1KeyPair, Error> {
    if let Some(key) = key_map.get(chain_id) {
        let chain_config = handle.config().map_err(BaseError::relayer)?;

        // try add the key to the chain handle, in case if it is only in the key map,
        // as for the case of integration tests.
        let _ = handle.add_key(
            chain_config.key_name,
            AnySigningKeyPair::Secp256k1(key.clone()),
        );

        return Ok(key.clone());
    }

    let keypair = handle.get_key().map_err(BaseError::relayer)?;

    let AnySigningKeyPair::Secp256k1(key) = keypair else {
        return Err(BaseError::generic(eyre!("no Secp256k1 key pair for chain {}", chain_id)).into());
    };

    Ok(key)
}
