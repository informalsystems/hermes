use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::builder::traits::cache::{
    HasChainACache, HasChainBCache, HasRelayAToBCache, HasRelayBToACache,
};
use crate::base::builder::traits::chain::{ChainABuilder, ChainBBuilder};
use crate::base::builder::traits::id::{HasTargetChainIds, HasTargetClientIds};
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
    ChainIdA<Context>: Ord,
    Context: HasChainACache + HasTargetChainIds + HasErrorType,
    InBuilder: ChainABuilder<Context>,
{
    async fn build_chain_a(context: &Context) -> Result<ChainA<Context>, Context::Error> {
        let chain_id = context.chain_id_a();
        let mut cache = Context::Runtime::acquire_mutex(context.chain_a_cache()).await;

        if let Some(chain) = cache.get(&chain_id) {
            Ok(chain.clone())
        } else {
            let chain = InBuilder::build_chain_a(context).await?;
            cache.insert(chain_id, chain.clone());

            Ok(chain)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> ChainBBuilder<Context> for BuildWithCache<InBuilder>
where
    ChainIdB<Context>: Ord,
    Context: HasChainBCache + HasTargetChainIds + HasErrorType,
    InBuilder: ChainBBuilder<Context>,
{
    async fn build_chain_b(context: &Context) -> Result<ChainB<Context>, Context::Error> {
        let chain_id = context.chain_id_b();
        let mut cache = Context::Runtime::acquire_mutex(context.chain_b_cache()).await;

        if let Some(chain) = cache.get(&chain_id) {
            Ok(chain.clone())
        } else {
            let chain = InBuilder::build_chain_b(context).await?;
            cache.insert(chain_id, chain.clone());

            Ok(chain)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> RelayAToBBuilder<Context> for BuildWithCache<InBuilder>
where
    ChainIdA<Context>: Ord,
    ChainIdB<Context>: Ord,
    ClientIdA<Context>: Ord,
    ClientIdB<Context>: Ord,
    Context: HasRelayAToBCache + HasTargetChainIds + HasTargetClientIds + HasErrorType,
    InBuilder: RelayAToBBuilder<Context>,
{
    async fn build_relay_a_to_b(context: &Context) -> Result<RelayAToB<Context>, Context::Error> {
        let chain_id_a = context.chain_id_a();
        let chain_id_b = context.chain_id_b();

        let client_id_a = context.client_id_a();
        let client_id_b = context.client_id_b();

        let relay_id = (chain_id_a, chain_id_b, client_id_a, client_id_b);

        let mut cache = Context::Runtime::acquire_mutex(context.relay_a_to_b_cache()).await;

        if let Some(relay) = cache.get(&relay_id) {
            Ok(relay.clone())
        } else {
            let relay = InBuilder::build_relay_a_to_b(context).await?;
            cache.insert(relay_id, relay.clone());

            Ok(relay)
        }
    }
}

#[async_trait]
impl<InBuilder, Context> RelayBToABuilder<Context> for BuildWithCache<InBuilder>
where
    ChainIdA<Context>: Ord,
    ChainIdB<Context>: Ord,
    ClientIdA<Context>: Ord,
    ClientIdB<Context>: Ord,
    Context: HasRelayBToACache + HasTargetChainIds + HasTargetClientIds + HasErrorType,
    InBuilder: RelayBToABuilder<Context>,
{
    async fn build_relay_b_to_a(context: &Context) -> Result<RelayBToA<Context>, Context::Error> {
        let chain_id_a = context.chain_id_a();
        let chain_id_b = context.chain_id_b();

        let client_id_a = context.client_id_a();
        let client_id_b = context.client_id_b();

        let relay_id = (chain_id_b, chain_id_a, client_id_b, client_id_a);

        let mut cache = Context::Runtime::acquire_mutex(context.relay_b_to_a_cache()).await;

        if let Some(relay) = cache.get(&relay_id) {
            Ok(relay.clone())
        } else {
            let relay = InBuilder::build_relay_b_to_a(context).await?;
            cache.insert(relay_id, relay.clone());

            Ok(relay)
        }
    }
}
