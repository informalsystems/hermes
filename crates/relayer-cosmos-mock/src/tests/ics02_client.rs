use crate::contexts::basecoin::MockBasecoin;
use crate::contexts::chain::MockCosmosContext;
use crate::tests::init::binary_setup;
use crate::types::error::Error;

use basecoin_store::impls::InMemoryStore;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_components::chain::traits::client::client_state::CanQueryClientState;
use ibc_relayer_components::chain::traits::client::create::CanBuildCreateClientPayload;
use ibc_relayer_components::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::components::message_sender::CanSendMessages;
use ibc_relayer_components::relay::traits::components::update_client_message_builder::CanBuildUpdateClientMessage;
use ibc_relayer_components::relay::traits::target::DestinationTarget;
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
        .send_messages(vec![msg_create_client])
        .await?;

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
        .send_messages(vec![msg_create_client])
        .await?;

    relayer
        .runtime()
        .sleep(tokio::time::Duration::from_millis(200))
        .await;

    let src_current_height = relayer.src_chain().query_chain_status().await?.height;

    let msg_update_client = relayer
        .build_update_client_messages(DestinationTarget, &src_current_height)
        .await?;

    relayer.dst_chain().send_messages(msg_update_client).await?;

    let latest_client_state =
        <MockCosmosContext<MockBasecoin<InMemoryStore>> as CanQueryClientState<
            MockCosmosContext<MockBasecoin<InMemoryStore>>,
        >>::query_client_state(relayer.dst_chain(), &ClientId::default())
        .await?;

    assert_eq!(latest_client_state.latest_height, src_current_height);

    Ok(())
}
