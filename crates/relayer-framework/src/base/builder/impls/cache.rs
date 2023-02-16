use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::cache::{
    HasChainACache, HasChainBCache, HasRelayAToBCache, HasRelayBToACache,
};
use crate::base::builder::traits::chain::{ChainABuilder, ChainBBuilder};
use crate::base::builder::traits::relay::{RelayAToBBuilder, RelayBToABuilder};
use crate::base::builder::types::aliases::{
    ChainA, ChainB, ChainIdA, ChainIdB, ClientIdA, ClientIdB, RelayAToB, RelayBToA,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::std_prelude::*;

pub struct BuildWithCache<InBuilder>(pub PhantomData<InBuilder>);

#[async_trait]
impl<InBuilder, Context> ChainABuilder<Context> for BuildWithCache<InBuilder>
where
    ChainA<Context>: Clone,
    ChainIdA<Context>: Ord + Clone,
    Context: HasChainACache + HasErrorType,
    InBuilder: ChainABuilder<Context>,
{
    async fn build_chain_a(
        context: &Context,
        chain_id: &ChainIdA<Context>,
    ) -> Result<ChainA<Context>, Context::Error> {
        let mut cache = Context::Runtime::acquire_mutex(context.chain_a_cache()).await;

        if let Some(chain) = cache.get(chain_id) {
            Ok(chain.clone())
        } else {
            let chain = InBuilder::build_chain_a(context, chain_id).await?;
            cache.insert(chain_id.clone(), chain.clone());

            Ok(chain)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> ChainBBuilder<Context> for BuildWithCache<InBuilder>
where
    ChainB<Context>: Clone,
    ChainIdB<Context>: Ord + Clone,
    Context: HasChainBCache + HasErrorType,
    InBuilder: ChainBBuilder<Context>,
{
    async fn build_chain_b(
        context: &Context,
        chain_id: &ChainIdB<Context>,
    ) -> Result<ChainB<Context>, Context::Error> {
        let mut cache = Context::Runtime::acquire_mutex(context.chain_b_cache()).await;

        if let Some(chain) = cache.get(chain_id) {
            Ok(chain.clone())
        } else {
            let chain = InBuilder::build_chain_b(context, chain_id).await?;
            cache.insert(chain_id.clone(), chain.clone());

            Ok(chain)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> RelayAToBBuilder<Context> for BuildWithCache<InBuilder>
where
    ChainIdA<Context>: Ord + Clone,
    ChainIdB<Context>: Ord + Clone,
    ClientIdA<Context>: Ord + Clone,
    ClientIdB<Context>: Ord + Clone,
    RelayAToB<Context>: Clone,
    Context: HasRelayAToBCache + HasErrorType,
    InBuilder: RelayAToBBuilder<Context>,
{
    async fn build_relay_a_to_b(
        context: &Context,
        src_chain_id: &ChainIdA<Context>,
        dst_chain_id: &ChainIdB<Context>,
        src_client_id: &ClientIdA<Context>,
        dst_client_id: &ClientIdB<Context>,
    ) -> Result<RelayAToB<Context>, Context::Error> {
        let relay_id = (
            src_chain_id.clone(),
            dst_chain_id.clone(),
            src_client_id.clone(),
            dst_client_id.clone(),
        );

        let mut cache = Context::Runtime::acquire_mutex(context.relay_a_to_b_cache()).await;

        if let Some(relay) = cache.get(&relay_id) {
            Ok(relay.clone())
        } else {
            let relay = InBuilder::build_relay_a_to_b(
                context,
                src_chain_id,
                dst_chain_id,
                src_client_id,
                dst_client_id,
            )
            .await?;
            cache.insert(relay_id, relay.clone());

            Ok(relay)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> RelayBToABuilder<Context> for BuildWithCache<InBuilder>
where
    ChainIdA<Context>: Ord + Clone,
    ChainIdB<Context>: Ord + Clone,
    ClientIdA<Context>: Ord + Clone,
    ClientIdB<Context>: Ord + Clone,
    RelayBToA<Context>: Clone,
    Context: HasRelayBToACache + HasErrorType,
    InBuilder: RelayBToABuilder<Context>,
{
    async fn build_relay_b_to_a(
        context: &Context,
        src_chain_id: &ChainIdB<Context>,
        dst_chain_id: &ChainIdA<Context>,
        src_client_id: &ClientIdB<Context>,
        dst_client_id: &ClientIdA<Context>,
    ) -> Result<RelayBToA<Context>, Context::Error> {
        let relay_id = (
            src_chain_id.clone(),
            dst_chain_id.clone(),
            src_client_id.clone(),
            dst_client_id.clone(),
        );

        let mut cache = Context::Runtime::acquire_mutex(context.relay_b_to_a_cache()).await;

        if let Some(relay) = cache.get(&relay_id) {
            Ok(relay.clone())
        } else {
            let relay = InBuilder::build_relay_b_to_a(
                context,
                src_chain_id,
                dst_chain_id,
                src_client_id,
                dst_client_id,
            )
            .await?;
            cache.insert(relay_id, relay.clone());

            Ok(relay)
        }
    }
}
