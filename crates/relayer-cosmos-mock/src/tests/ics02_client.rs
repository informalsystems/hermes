use crate::contexts::basecoin::MockBasecoin;
use crate::contexts::chain::MockCosmosContext;
use crate::tests::init::binary_setup;
use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;

use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_components::chain::traits::client::create::CanBuildCreateClientPayload;
use ibc_relayer_components::relay::traits::target::SourceTarget;
use ibc_relayer_components::relay::traits::update_client::CanBuildUpdateClientMessage;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

#[tokio::test]
async fn test_create_client() -> Result<(), Error> {
    let relayer = binary_setup().await;

    let msg_create_client =
        <MockCosmosContext<MockBasecoin<InMemoryStore>> as CanBuildCreateClientPayload<
            MockCosmosContext<MockBasecoin<InMemoryStore>>,
        >>::build_create_client_payload(relayer.src_chain(), &())
        .await?;

    relayer
        .dst_chain()
        .submit_messages(vec![msg_create_client])?;

    assert!(relayer
        .dst_chain()
        .ibc_context()
        .client_state(&ClientId::default())
        .is_ok());

    Ok(())
}

#[tokio::test]
async fn test_update_client() -> Result<(), Error> {
    let relayer = binary_setup().await;

    let msg_create_client =
        <MockCosmosContext<MockBasecoin<InMemoryStore>> as CanBuildCreateClientPayload<
            MockCosmosContext<MockBasecoin<InMemoryStore>>,
        >>::build_create_client_payload(relayer.src_chain(), &())
        .await?;

    relayer
        .dst_chain()
        .submit_messages(vec![msg_create_client])?;

    relayer
        .runtime()
        .sleep(tokio::time::Duration::from_millis(200))
        .await;

    let src_current_height = relayer.src_chain().get_current_height();

    let msg_update_client = relayer
        .build_update_client_messages(SourceTarget, &src_current_height)
        .await?;

    relayer.dst_chain().submit_messages(msg_update_client)?;

    Ok(())
}
