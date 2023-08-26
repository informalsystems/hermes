use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_components::relay::traits::target::SourceTarget;
use ibc_relayer_components::relay::traits::update_client::CanBuildUpdateClientMessage;

use crate::tests::init::init_binary_stand;
use crate::traits::handler::ChainHandler;
use crate::types::error::Error;

#[tokio::test]
async fn test_create_client() -> Result<(), Error> {
    let builder = init_binary_stand();

    tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;

    let msg_create_client = builder.chains[0].build_msg_create_client().await?;

    builder.chains[1]
        .submit_messages(vec![msg_create_client])
        .await?;

    assert!(builder.chains[1]
        .ibc_context()
        .client_state(&ClientId::default())
        .is_ok());

    builder.stop();

    Ok(())
}

#[tokio::test]
async fn test_update_client() -> Result<(), Error> {
    let builder = init_binary_stand();

    tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;

    let msg_create_client = builder.chains[0].build_msg_create_client().await?;

    builder.chains[1]
        .submit_messages(vec![msg_create_client])
        .await?;

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let src_current_height = builder.chains[0].get_current_height();

    let msg_update_client = builder.relayers[0]
        .build_update_client_messages(SourceTarget, &src_current_height)
        .await?;

    builder.relayers[0]
        .dst_chain()
        .submit_messages(msg_update_client)
        .await?;

    builder.stop();

    Ok(())
}
