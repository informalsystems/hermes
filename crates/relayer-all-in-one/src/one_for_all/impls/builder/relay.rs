use async_trait::async_trait;
use ibc_relayer_components::build::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use ibc_relayer_components_extra::build::traits::components::relay_with_batch_builder::RelayWithBatchBuilder;

use crate::one_for_all::traits::builder::{
    ChainA, ChainB, ClientIdA, ClientIdB, OfaBuilder, RelayAToB, RelayBToA, RelayError,
};
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::one_for_all::types::builder::OfaBuilderWrapper;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Build> RelayWithBatchBuilder<OfaBuilderWrapper<Build>, RelayAToBTarget> for OfaComponents
where
    Build: OfaBuilder,
{
    async fn build_relay_with_batch(
        build: &OfaBuilderWrapper<Build>,
        src_client_id: &ClientIdA<Build>,
        dst_client_id: &ClientIdB<Build>,
        src_chain: OfaChainWrapper<ChainA<Build>>,
        dst_chain: OfaChainWrapper<ChainB<Build>>,
        src_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
    ) -> Result<OfaRelayWrapper<RelayAToB<Build>>, Build::Error> {
        let relay_a_to_b = OfaBuilder::build_relay_a_to_b(
            build.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await?;

        Ok(OfaRelayWrapper::new(relay_a_to_b))
    }
}

#[async_trait]
impl<Build> RelayWithBatchBuilder<OfaBuilderWrapper<Build>, RelayBToATarget> for OfaComponents
where
    Build: OfaBuilder,
{
    async fn build_relay_with_batch(
        build: &OfaBuilderWrapper<Build>,
        src_client_id: &ClientIdB<Build>,
        dst_client_id: &ClientIdA<Build>,
        src_chain: OfaChainWrapper<ChainB<Build>>,
        dst_chain: OfaChainWrapper<ChainA<Build>>,
        src_batch_sender: MessageBatchSender<ChainB<Build>, RelayError<Build>>,
        dst_batch_sender: MessageBatchSender<ChainA<Build>, RelayError<Build>>,
    ) -> Result<OfaRelayWrapper<RelayBToA<Build>>, Build::Error> {
        let relay_b_to_a = OfaBuilder::build_relay_b_to_a(
            build.builder.as_ref(),
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await?;

        Ok(OfaRelayWrapper::new(relay_b_to_a))
    }
}
