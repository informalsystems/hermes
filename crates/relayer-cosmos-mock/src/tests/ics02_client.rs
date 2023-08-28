use crate::contexts::basecoin::MockBasecoin;
use crate::contexts::chain::MockCosmosContext;
use crate::tests::init::mock_basecoin_binary_stand;
use crate::types::error::Error;

use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_components::chain::traits::client::create::CanBuildCreateClientPayload;
use ibc_relayer_components::relay::traits::target::SourceTarget;
use ibc_relayer_components::relay::traits::update_client::CanBuildUpdateClientMessage;

#[tokio::test]
async fn test_create_client() -> Result<(), Error> {
    let (src_chain_ctx, dst_chain_ctx, _) = mock_basecoin_binary_stand();

    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;

    let msg_create_client =
        <MockCosmosContext<MockBasecoin<InMemoryStore>> as CanBuildCreateClientPayload<
            MockCosmosContext<MockBasecoin<InMemoryStore>>,
        >>::build_create_client_payload(&src_chain_ctx, &())
        .await?;

    dst_chain_ctx.submit_messages(vec![msg_create_client])?;

    assert!(dst_chain_ctx
        .ibc_context()
        .client_state(&ClientId::default())
        .is_ok());

    Ok(())
}

#[tokio::test]
async fn test_update_client() -> Result<(), Error> {
    let (src_chain_ctx, dst_chain_ctx, relayer) = mock_basecoin_binary_stand();

    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;

    let msg_create_client =
        <MockCosmosContext<MockBasecoin<InMemoryStore>> as CanBuildCreateClientPayload<
            MockCosmosContext<MockBasecoin<InMemoryStore>>,
        >>::build_create_client_payload(&src_chain_ctx, &())
        .await?;

    dst_chain_ctx.submit_messages(vec![msg_create_client])?;

    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;

    let src_current_height = src_chain_ctx.get_current_height();

    let msg_update_client = relayer
        .build_update_client_messages(SourceTarget, &src_current_height)
        .await?;

    relayer.dst_chain().submit_messages(msg_update_client)?;

    Ok(())
}
