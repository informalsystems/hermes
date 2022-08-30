//! Protocol logic specific to processing ICS2 messages of type `MsgUpdateAnyClient`.
use core::fmt::Debug;

use crate::clients::host_functions::HostFunctionsProvider;
use crate::core::ics02_client::client_def::{AnyClient, ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::events::Attributes;
use crate::core::ics02_client::handler::ClientResult;
use crate::core::ics02_client::height::Height;
use crate::core::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use crate::core::ics24_host::identifier::ClientId;
use crate::core::ics26_routing::context::ReaderContext;
use crate::events::IbcEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::prelude::*;
use crate::timestamp::Timestamp;

/// The result following the successful processing of a `MsgUpdateAnyClient` message. Preferably
/// this data type should be used with a qualified name `update_client::Result` to avoid ambiguity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Result {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: Option<ConsensusUpdateResult>,
    pub processed_time: Timestamp,
    pub processed_height: Height,
}

pub fn process<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    msg: MsgUpdateAnyClient,
) -> HandlerResult<ClientResult, Error> {
    let mut output = HandlerOutput::builder();

    let MsgUpdateAnyClient {
        client_id,
        header,
        signer: _,
    } = msg;

    // Read client type from the host chain store. The client should already exist.
    let client_type = ctx.client_type(&client_id)?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_type);

    // Read client state from the host chain store.
    let client_state = ctx.client_state(&client_id)?;

    if client_state.is_frozen() {
        return Err(Error::client_frozen(client_id));
    }

    // Read consensus state from the host chain store.
    let latest_consensus_state = ctx
        .consensus_state(&client_id, client_state.latest_height())
        .map_err(|_| {
            Error::consensus_state_not_found(client_id.clone(), client_state.latest_height())
        })?;

    tracing::debug!("latest consensus state: {:?}", latest_consensus_state);

    let now = ctx.host_timestamp();
    let duration = now
        .duration_since(&latest_consensus_state.timestamp())
        .ok_or_else(|| {
            Error::invalid_consensus_state_timestamp(latest_consensus_state.timestamp(), now)
        })?;

    if client_state.expired(duration) {
        return Err(Error::header_not_within_trust_period(
            latest_consensus_state.timestamp(),
            now,
        ));
    }

    client_def
        .verify_header(ctx, client_id.clone(), client_state.clone(), header.clone())
        .map_err(|e| Error::header_verification_failure(e.to_string()))?;

    let found_misbehaviour = client_def
        .check_for_misbehaviour(ctx, client_id.clone(), client_state.clone(), header.clone())
        .map_err(|e| Error::header_verification_failure(e.to_string()))?;

    let event_attributes = Attributes {
        client_id: client_id.clone(),
        height: ctx.host_height(),
        client_type,
        consensus_height: client_state.latest_height(),
    };

    if found_misbehaviour {
        let client_state = client_def.update_state_on_misbehaviour(client_state, header)?;
        let result = ClientResult::Update(Result {
            client_id,
            client_state,
            consensus_state: None,
            processed_time: ctx.host_timestamp(),
            processed_height: ctx.host_height(),
        });
        output.emit(IbcEvent::ClientMisbehaviour(event_attributes.into()));
        return Ok(output.with_result(result));
    }
    // Use client_state to validate the new header against the latest consensus_state.
    // This function will return the new client_state (its latest_height changed) and a
    // consensus_state obtained from header. These will be later persisted by the keeper.
    let (new_client_state, new_consensus_state) = client_def
        .update_state(ctx, client_id.clone(), client_state, header)
        .map_err(|e| Error::header_verification_failure(e.to_string()))?;

    let result = ClientResult::Update(Result {
        client_id,
        client_state: new_client_state,
        consensus_state: Some(new_consensus_state),
        processed_time: ctx.host_timestamp(),
        processed_height: ctx.host_height(),
    });

    output.emit(IbcEvent::UpdateClient(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use crate::clients::ics11_beefy::header::ParachainHeadersWithProof;
    use core::str::FromStr;
    use subxt::sp_runtime::traits::Header;
    use test_log::test;

    use crate::core::ics02_client::client_consensus::{AnyConsensusState, ConsensusState};
    use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics02_client::context::{ClientKeeper, ClientReader};
    use crate::core::ics02_client::error::{Error, ErrorDetail};
    use crate::core::ics02_client::handler::dispatch;
    use crate::core::ics02_client::handler::ClientResult::Update;
    use crate::core::ics02_client::header::AnyHeader;
    use crate::core::ics02_client::msgs::create_client::MsgCreateAnyClient;
    use crate::core::ics02_client::msgs::update_client::MsgUpdateAnyClient;
    use crate::core::ics02_client::msgs::ClientMsg;
    use crate::core::ics24_host::identifier::{ChainId, ClientId};
    use crate::events::IbcEvent;
    use crate::handler::HandlerOutput;
    use crate::mock::client_state::MockClientState;
    use crate::mock::context::MockContext;
    use crate::mock::header::MockHeader;
    use crate::mock::host::HostType;
    use crate::prelude::*;
    use crate::test_utils::{get_dummy_account_id, Crypto};
    use crate::timestamp::Timestamp;
    use crate::Height;

    #[test]
    fn test_update_client_ok() {
        let client_id = ClientId::default();
        let signer = get_dummy_account_id();

        let timestamp = Timestamp::now();

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42));
        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: MockHeader::new(Height::new(0, 46))
                .with_timestamp(timestamp)
                .into(),
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert_eq!(event.height(), ctx.host_height());
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert_eq!(
                            upd_res.client_state,
                            AnyClientState::Mock(MockClientState::new(
                                MockHeader::new(msg.header.height()).with_timestamp(timestamp)
                            ))
                        )
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_nonexisting_client() {
        let client_id = ClientId::from_str("mockclient1").unwrap();
        let signer = get_dummy_account_id();

        let ctx = MockContext::default().with_client(&client_id, Height::new(0, 42));

        let msg = MsgUpdateAnyClient {
            client_id: ClientId::from_str("nonexistingclient").unwrap(),
            header: MockHeader::new(Height::new(0, 46)).into(),
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Err(Error(ErrorDetail::ClientNotFound(e), _)) => {
                assert_eq!(e.client_id, msg.client_id);
            }
            _ => {
                panic!("expected ClientNotFound error, instead got {:?}", output)
            }
        }
    }

    #[test]
    fn test_update_client_ok_multiple() {
        let client_ids = vec![
            ClientId::from_str("mockclient1").unwrap(),
            ClientId::from_str("mockclient2").unwrap(),
            ClientId::from_str("mockclient3").unwrap(),
        ];
        let signer = get_dummy_account_id();
        let initial_height = Height::new(0, 45);
        let update_height = Height::new(0, 49);

        let mut ctx = MockContext::default();

        for cid in &client_ids {
            ctx = ctx.with_client(cid, initial_height);
        }

        for cid in &client_ids {
            let msg = MsgUpdateAnyClient {
                client_id: cid.clone(),
                header: MockHeader::new(update_height).into(),
                signer: signer.clone(),
            };

            let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

            match output {
                Ok(HandlerOutput {
                    result: _,
                    mut events,
                    log,
                }) => {
                    assert_eq!(events.len(), 1);
                    let event = events.pop().unwrap();
                    assert!(
                        matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                    );
                    assert_eq!(event.height(), ctx.host_height());
                    assert!(log.is_empty());
                }
                Err(err) => {
                    panic!("unexpected error: {}", err);
                }
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_adjacent_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20);
        let update_height = Height::new(1, 21);

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            Height::new(1, 1),
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            update_height,
        );

        let signer = get_dummy_account_id();

        let block_ref = ctx_b.host_block(update_height);
        let mut latest_header: AnyHeader = block_ref.cloned().map(Into::into).unwrap();

        latest_header = match latest_header {
            AnyHeader::Tendermint(mut theader) => {
                theader.trusted_height = client_height;
                AnyHeader::Tendermint(theader)
            }
            AnyHeader::Beefy(h) => AnyHeader::Beefy(h),
            AnyHeader::Mock(m) => AnyHeader::Mock(m),
        };

        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: latest_header,
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert_eq!(event.height(), ctx.host_height());
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state.latest_height(), msg.header.height(),)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_non_adjacent_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20);
        let update_height = Height::new(1, 21);

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            Height::new(1, 1),
        )
        .with_client_parametrized_history(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            update_height,
        );

        let signer = get_dummy_account_id();

        let block_ref = ctx_b.host_block(update_height);
        let mut latest_header: AnyHeader = block_ref.cloned().map(Into::into).unwrap();

        let trusted_height = client_height.clone().sub(1).unwrap_or_default();

        latest_header = match latest_header {
            AnyHeader::Tendermint(mut theader) => {
                theader.trusted_height = trusted_height;
                AnyHeader::Tendermint(theader)
            }
            AnyHeader::Beefy(h) => AnyHeader::Beefy(h),
            AnyHeader::Mock(m) => AnyHeader::Mock(m),
        };

        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: latest_header,
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert_eq!(event.height(), ctx.host_height());
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state.latest_height(), msg.header.height(),)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_duplicate_ok() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20);

        let chain_start_height = Height::new(1, 11);

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            chain_start_height,
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            client_height,
        );

        let signer = get_dummy_account_id();

        let block_ref = ctx_b.host_block(client_height);
        let latest_header: AnyHeader = match block_ref.cloned().map(Into::into).unwrap() {
            AnyHeader::Tendermint(mut theader) => {
                let cons_state = ctx.latest_consensus_states(&client_id, &client_height);
                if let AnyConsensusState::Tendermint(tcs) = cons_state {
                    theader.signed_header.header.time = tcs.timestamp;
                    theader.trusted_height = Height::new(1, 11)
                }
                AnyHeader::Tendermint(theader)
            }
            AnyHeader::Beefy(h) => AnyHeader::Beefy(h),
            AnyHeader::Mock(header) => AnyHeader::Mock(header),
        };

        let msg = MsgUpdateAnyClient {
            client_id: client_id.clone(),
            header: latest_header,
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

        match output {
            Ok(HandlerOutput {
                result,
                mut events,
                log,
            }) => {
                assert_eq!(events.len(), 1);
                let event = events.pop().unwrap();
                assert!(
                    matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                );
                assert_eq!(event.height(), ctx.host_height());
                assert!(log.is_empty());
                // Check the result
                match result {
                    Update(upd_res) => {
                        assert_eq!(upd_res.client_id, client_id);
                        assert!(!upd_res.client_state.is_frozen());
                        assert_eq!(upd_res.client_state, ctx.latest_client_states(&client_id));
                        assert_eq!(upd_res.client_state.latest_height(), msg.header.height(),)
                    }
                    _ => panic!("update handler result has incorrect type"),
                }
            }
            Err(err) => {
                panic!("unexpected error: {:?}", err);
            }
        }
    }

    #[test]
    fn test_update_synthetic_tendermint_client_lower_height() {
        let client_id = ClientId::new(ClientType::Tendermint, 0).unwrap();
        let client_height = Height::new(1, 20);

        let client_update_height = Height::new(1, 19);

        let chain_start_height = Height::new(1, 11);

        let ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            chain_start_height,
        )
        .with_client_parametrized(
            &client_id,
            client_height,
            Some(ClientType::Tendermint), // The target host chain (B) is synthetic TM.
            Some(client_height),
        );

        let ctx_b = MockContext::new(
            ChainId::new("mockgaiaB".to_string(), 1),
            HostType::SyntheticTendermint,
            5,
            client_height,
        );

        let signer = get_dummy_account_id();

        let block_ref = ctx_b.host_block(client_update_height);
        let latest_header: AnyHeader = block_ref.cloned().map(Into::into).unwrap();

        let msg = MsgUpdateAnyClient {
            client_id,
            header: latest_header,
            signer,
        };

        let output = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg));

        match output {
            Ok(_) => {
                panic!("update handler result has incorrect type");
            }
            Err(err) => match err.detail() {
                ErrorDetail::HeaderVerificationFailure(_) => {}
                _ => panic!("unexpected error: {:?}", err),
            },
        }
    }

    #[cfg(feature = "ics11_beefy")]
    #[tokio::test]
    async fn test_continuous_update_of_beefy_client() {
        use crate::clients::ics11_beefy::client_state::ClientState as BeefyClientState;
        use crate::clients::ics11_beefy::consensus_state::ConsensusState;
        use crate::clients::ics11_beefy::header::BeefyHeader;
        use crate::clients::ics11_beefy::header::ParachainHeader as BeefyParachainHeader;
        use beefy_client_primitives::NodesUtils;
        use beefy_client_primitives::PartialMmrLeaf;
        use beefy_queries::runtime;
        use beefy_queries::{
            helpers::{fetch_timestamp_extrinsic_with_proof, TimeStampExtWithProof},
            ClientWrapper,
        };
        use codec::{Decode, Encode};
        use subxt::rpc::{rpc_params, JsonValue, Subscription, SubscriptionClientT};

        let client_id = ClientId::new(ClientType::Beefy, 0).unwrap();

        let chain_start_height = Height::new(1, 11);

        let mut ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Beefy,
            5,
            chain_start_height,
        );

        let signer = get_dummy_account_id();

        let url = std::env::var("NODE_ENDPOINT").unwrap_or("ws://127.0.0.1:9944".to_string());
        let client = subxt::ClientBuilder::new()
            .set_url(url)
            .build::<subxt::DefaultConfig>()
            .await
            .unwrap();

        let para_url = std::env::var("NODE_ENDPOINT").unwrap_or("ws://127.0.0.1:9988".to_string());
        let para_client = subxt::ClientBuilder::new()
            .set_url(para_url)
            .build::<subxt::DefaultConfig>()
            .await
            .unwrap();
        let client_wrapper = ClientWrapper {
            relay_client: client.clone(),
            para_client: para_client.clone(),
            beefy_activation_block: 0,
            para_id: 2001,
        };

        let mut count = 0;
        let (client_state, consensus_state) = loop {
            let beefy_state = client_wrapper
                .construct_beefy_client_state(0)
                .await
                .unwrap();

            let api =
                client_wrapper
                    .relay_client
                    .clone()
                    .to_runtime_api::<runtime::api::RuntimeApi<
                        subxt::DefaultConfig,
                        subxt::PolkadotExtrinsicParams<_>,
                    >>();
            let subxt_block_number: subxt::BlockNumber = beefy_state.latest_beefy_height.into();
            let block_hash = client_wrapper
                .relay_client
                .rpc()
                .block_hash(Some(subxt_block_number))
                .await
                .unwrap();
            let head_data = api
                .storage()
                .paras()
                .heads(
                    &runtime::api::runtime_types::polkadot_parachain::primitives::Id(
                        client_wrapper.para_id,
                    ),
                    block_hash,
                )
                .await
                .unwrap()
                .unwrap();
            let decoded_para_head = frame_support::sp_runtime::generic::Header::<
                u32,
                frame_support::sp_runtime::traits::BlakeTwo256,
            >::decode(&mut &*head_data.0)
            .unwrap();
            let block_number = decoded_para_head.number;
            let client_state = BeefyClientState {
                chain_id: ChainId::new("relay-chain".to_string(), 0),
                relay_chain: Default::default(),
                mmr_root_hash: beefy_state.mmr_root_hash,
                latest_beefy_height: beefy_state.latest_beefy_height,
                frozen_height: None,
                beefy_activation_block: beefy_state.beefy_activation_block,
                latest_para_height: block_number,
                para_id: client_wrapper.para_id,
                authority: beefy_state.current_authorities,
                next_authority_set: beefy_state.next_authorities,
            };
            // we can't use the genesis block to construct the initial state.
            if block_number == 0 {
                continue;
            }
            let subxt_block_number: subxt::BlockNumber = block_number.into();
            let block_hash = client_wrapper
                .para_client
                .rpc()
                .block_hash(Some(subxt_block_number))
                .await
                .unwrap();

            let TimeStampExtWithProof {
                ext: timestamp_extrinsic,
                proof: extrinsic_proof,
            } = fetch_timestamp_extrinsic_with_proof(&client_wrapper.para_client, block_hash)
                .await
                .unwrap();
            let parachain_header = BeefyParachainHeader {
                parachain_header: decoded_para_head,
                partial_mmr_leaf: PartialMmrLeaf {
                    version: Default::default(),
                    parent_number_and_hash: Default::default(),
                    beefy_next_authority_set: Default::default(),
                },
                parachain_heads_proof: vec![],
                heads_leaf_index: 0,
                heads_total_count: 0,
                extrinsic_proof,
                timestamp_extrinsic,
            };

            let consensus_state = ConsensusState::from_header(parachain_header)
                .unwrap()
                .wrap_any();

            break (client_state.wrap_any(), consensus_state);
        };

        let create_client = MsgCreateAnyClient {
            client_state,
            consensus_state,
            signer: signer.clone(),
        };

        // Create the client
        let res = dispatch::<_, Crypto>(&ctx, ClientMsg::CreateClient(create_client)).unwrap();
        ctx.store_client_result(res.result).unwrap();
        let mut subscription: Subscription<String> = client
            .rpc()
            .client
            .subscribe(
                "beefy_subscribeJustifications",
                rpc_params![],
                "beefy_unsubscribeJustifications",
            )
            .await
            .unwrap();

        while let Some(Ok(commitment)) = subscription.next().await {
            if count == 100 {
                break;
            }
            let recv_commitment: sp_core::Bytes =
                serde_json::from_value(JsonValue::String(commitment)).unwrap();
            let signed_commitment: beefy_primitives::SignedCommitment<
                u32,
                beefy_primitives::crypto::Signature,
            > = codec::Decode::decode(&mut &*recv_commitment).unwrap();
            let client_state: BeefyClientState = match ctx.client_state(&client_id).unwrap() {
                AnyClientState::Beefy(client_state) => client_state,
                _ => panic!("unexpected client state"),
            };
            match signed_commitment.commitment.validator_set_id {
                id if id < client_state.authority.id => {
                    // If validator set id of signed commitment is less than current validator set id we have
                    // Then commitment is outdated and we skip it.
                    println!(
                        "Skipping outdated commitment \n Received signed commitmment with validator_set_id: {:?}\n Current authority set id: {:?}\n Next authority set id: {:?}\n",
                        signed_commitment.commitment.validator_set_id, client_state.authority.id, client_state.next_authority_set.id
                    );
                    continue;
                }
                _ => {}
            }

            println!(
                "Received signed commitmment for: {:?}",
                signed_commitment.commitment.block_number
            );

            let block_number = signed_commitment.commitment.block_number;
            let headers = client_wrapper
                .query_finalized_parachain_headers_at(
                    block_number,
                    client_state.latest_beefy_height,
                )
                .await
                .unwrap();
            let (parachain_headers, batch_proof) = client_wrapper
                .query_finalized_parachain_headers_with_proof(
                    block_number,
                    client_state.latest_beefy_height,
                    headers.iter().map(|h| *h.number()).collect(),
                )
                .await
                .unwrap();

            let mmr_update = client_wrapper
                .fetch_mmr_update_proof_for(signed_commitment.clone())
                .await
                .unwrap();

            let mmr_size = NodesUtils::new(batch_proof.leaf_count).size();

            let header = BeefyHeader {
                headers_with_proof: Some(ParachainHeadersWithProof {
                    headers: parachain_headers
                        .into_iter()
                        .map(|header| BeefyParachainHeader {
                            parachain_header: Decode::decode(
                                &mut &*header.parachain_header.as_slice(),
                            )
                            .unwrap(),
                            partial_mmr_leaf: header.partial_mmr_leaf,
                            parachain_heads_proof: header.parachain_heads_proof,
                            heads_leaf_index: header.heads_leaf_index,
                            heads_total_count: header.heads_total_count,
                            extrinsic_proof: header.extrinsic_proof,
                            timestamp_extrinsic: header.timestamp_extrinsic,
                        })
                        .collect(),
                    mmr_proofs: batch_proof
                        .items
                        .into_iter()
                        .map(|item| item.encode())
                        .collect(),
                    mmr_size,
                }),
                mmr_update_proof: Some(mmr_update),
            };

            let msg = MsgUpdateAnyClient {
                client_id: client_id.clone(),
                header: AnyHeader::Beefy(header),
                signer: signer.clone(),
            };

            let res = dispatch::<_, Crypto>(&ctx, ClientMsg::UpdateClient(msg.clone()));

            match res {
                Ok(HandlerOutput {
                    result,
                    mut events,
                    log,
                }) => {
                    assert_eq!(events.len(), 1);
                    let event = events.pop().unwrap();
                    assert!(
                        matches!(event, IbcEvent::UpdateClient(ref e) if e.client_id() == &msg.client_id)
                    );
                    assert_eq!(event.height(), ctx.host_height());
                    assert!(log.is_empty());
                    ctx.store_client_result(result.clone()).unwrap();
                    match result {
                        Update(upd_res) => {
                            assert_eq!(upd_res.client_id, client_id);
                            assert!(!upd_res.client_state.is_frozen());
                            assert_eq!(
                                upd_res.client_state,
                                ctx.latest_client_states(&client_id).clone()
                            );
                        }
                        _ => panic!("update handler result has incorrect type"),
                    }
                }
                Err(e) => panic!("Unexpected error {:?}", e),
            }
            println!("Updated client successfully");
            count += 1;
        }
    }
}
