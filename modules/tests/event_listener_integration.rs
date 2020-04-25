
/// Event Listenr integration tests.
///
/// These are all ignored by default, since they test against running
/// against a running IBC network. This can be setup by running `./dev-env` in github.com/iqlusioninc/relayer
///
/// ```
/// cargo test -- --ignored
/// ```


mod ibc_events{
    use tendermint::rpc::event_listener::EventListener;
    use relayer_modules::ics02_client::events::*;
    use std::convert::TryFrom;




    async fn create_event_listener()->EventListener {
        tendermint::rpc::event_listener::EventListener::connect(
            "tcp://127.0.0.1:26657".parse().unwrap()
        ).await.unwrap()
    }

    /// Create Client event
    #[tokio::test]
    // #[ig nore]
    async fn test_create_client_event(){
        let mut client = create_event_listener().await;
        let _ = client.subscribe("tm.event='Tx'".to_owned()).await.unwrap();

        let mut x:i32 = 0;
        loop{
            match CreateClientEvent::try_from(client.get_event().await.unwrap()){
                Ok(event) =>{ dbg!(&event); break;},
                Err(err) => {dbg!(err);},
            }
            if x ==99{
                panic!("No Create Client Event found")
            }
            x +=1;
        }

    }

}