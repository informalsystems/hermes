use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;

use crate::tests::init::init_binary_stand;
use crate::traits::handler::ChainHandler;
use crate::types::error::Error;

#[tokio::test]
async fn test_create_client() -> Result<(), Error> {
    let builder = init_binary_stand();

    tokio::time::sleep(tokio::time::Duration::from_millis(2500)).await;

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

    tokio::time::sleep(tokio::time::Duration::from_millis(2500)).await;

    let msg_create_client = builder.chains[0].build_msg_create_client().await?;

    builder.chains[1]
        .submit_messages(vec![msg_create_client])
        .await?;

    tokio::time::sleep(tokio::time::Duration::from_millis(2000)).await;

    let msg_update_client = builder.chains[0].build_msg_update_client().await?;

    builder.chains[1]
        .submit_messages(vec![msg_update_client])
        .await?;

    builder.stop();

    Ok(())
}
