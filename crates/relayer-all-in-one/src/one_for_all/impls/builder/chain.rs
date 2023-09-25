use async_trait::async_trait;
use ibc_relayer_components::build::traits::components::chain_builder::ChainBuilder;
use ibc_relayer_components::build::traits::target::chain::{ChainATarget, ChainBTarget};

use crate::one_for_all::traits::builder::{ChainA, ChainB, ChainIdA, ChainIdB, OfaBuilder};
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::std_prelude::*;

#[async_trait]
impl<Builder> ChainBuilder<OfaBuilderWrapper<Builder>, ChainATarget> for OfaComponents
where
    Builder: OfaBuilder,
{
    async fn build_chain(
        builder: &OfaBuilderWrapper<Builder>,
        chain_id: &ChainIdA<Builder>,
    ) -> Result<OfaChainWrapper<ChainA<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_a(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}

#[async_trait]
impl<Builder> ChainBuilder<OfaBuilderWrapper<Builder>, ChainBTarget> for OfaComponents
where
    Builder: OfaBuilder,
{
    async fn build_chain(
        builder: &OfaBuilderWrapper<Builder>,
        chain_id: &ChainIdB<Builder>,
    ) -> Result<OfaChainWrapper<ChainB<Builder>>, Builder::Error> {
        let chain = builder.builder.build_chain_b(chain_id).await?;

        Ok(OfaChainWrapper::new(chain))
    }
}
