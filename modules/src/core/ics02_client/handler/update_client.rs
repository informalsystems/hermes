//! Protocol logic specific to processing ICS2 messages of type `MsgUpdateAnyClient`.
use tracing::debug;

use crate::clients::crypto_ops::crypto::CryptoOps;
use crate::core::ics02_client::client_def::{AnyClient, ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::events::Attributes;
use crate::core::ics02_client::handler::ClientResult;
use crate::core::ics02_client::height::Height;
use crate::core::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use crate::core::ics24_host::identifier::ClientId;
use crate::core::ics26_routing::context::LightClientContext;
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

pub fn process<Crypto: CryptoOps>(
    ctx: &dyn LightClientContext,
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

    let client_def = AnyClient::<Crypto>::from_client_type(client_type);

    // Read client state from the host chain store.
    let client_state = ctx.client_state(&client_id)?;

    if client_state.is_frozen() {
        return Err(Error::client_frozen(client_id));
    }

    if client_type != ClientType::Beefy {
        // Read consensus state from the host chain store.
        let latest_consensus_state = ctx
            .consensus_state(&client_id, client_state.latest_height())
            .map_err(|_| {
                Error::consensus_state_not_found(client_id.clone(), client_state.latest_height())
            })?;

        debug!("latest consensus state: {:?}", latest_consensus_state);

        let now = ctx.host_timestamp();
        let duration = now
            .duration_since(&latest_consensus_state.timestamp())
            .ok_or_else(|| {
                Error::invalid_consensus_state_timestamp(latest_consensus_state.timestamp(), now)
            })?;

        if client_state.expired(duration) {
            return Err(Error::header_not_within_trust_period(
                latest_consensus_state.timestamp(),
                header.timestamp(),
            ));
        }
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
        ..Default::default()
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
    use core::str::FromStr;
    use test_log::test;

    use crate::clients::ics11_beefy::client_state::ClientState as BeefyClientState;
    use crate::clients::ics11_beefy::header::BeefyHeader;
    use crate::clients::ics11_beefy::polkadot_runtime as runtime;
    use crate::core::ics02_client::client_consensus::AnyConsensusState;
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
    use beefy_primitives::mmr::BeefyNextAuthoritySet;
    use hex_literal::hex;
    use sp_core::H256;

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

    use crate::clients::ics11_beefy::header::ParachainHeader as BeefyParachainHeader;
    use beefy_client::primitives::{
        MmrLeaf, MmrUpdateProof, ParachainHeader, PartialMmrLeaf, SignatureWithAuthorityIndex,
        SignedCommitment,
    };
    use beefy_client::{MerkleHasher, NodesUtils};
    use codec::{Decode, Encode};
    use sp_core::keccak_256;
    use sp_runtime::traits::Convert;
    use std::collections::BTreeMap;
    use subxt::rpc::ClientT;
    use subxt::rpc::{rpc_params, JsonValue, Subscription, SubscriptionClientT};

    const PARA_ID: u32 = 2000;

    /// Construct the mmr update for beefy light client
    async fn get_mmr_update(
        client: &subxt::Client<subxt::DefaultConfig>,
        signed_commitment: beefy_primitives::SignedCommitment<
            u32,
            beefy_primitives::crypto::Signature,
        >,
    ) -> MmrUpdateProof {
        let api =
            client.clone().to_runtime_api::<runtime::api::RuntimeApi<
                subxt::DefaultConfig,
                subxt::PolkadotExtrinsicParams<_>,
            >>();
        let subxt_block_number: subxt::BlockNumber =
            signed_commitment.commitment.block_number.into();
        let block_hash = client
            .rpc()
            .block_hash(Some(subxt_block_number))
            .await
            .unwrap();

        let current_authorities = api.storage().beefy().authorities(block_hash).await.unwrap();

        // Current LeafIndex
        let block_number = signed_commitment.commitment.block_number;
        let leaf_index = (block_number - 1) as u64;
        let leaf_proof: pallet_mmr_rpc::LeafProof<H256> = client
            .rpc()
            .client
            .request("mmr_generateProof", rpc_params!(leaf_index, block_hash))
            .await
            .unwrap();

        let opaque_leaf: Vec<u8> = codec::Decode::decode(&mut &*leaf_proof.leaf.0).unwrap();
        let latest_leaf: MmrLeaf<u32, H256, H256, H256> =
            codec::Decode::decode(&mut &*opaque_leaf).unwrap();
        let mmr_proof: pallet_mmr_primitives::Proof<H256> =
            codec::Decode::decode(&mut &*leaf_proof.proof.0).unwrap();

        let authority_address_hashes = current_authorities
            .into_iter()
            .map(|x| {
                let id: beefy_primitives::crypto::AuthorityId =
                    codec::Decode::decode(&mut &*x.encode()).unwrap();
                keccak_256(&beefy_mmr::BeefyEcdsaToEthereum::convert(id))
            })
            .collect::<Vec<_>>();

        let signatures = signed_commitment
            .signatures
            .into_iter()
            .enumerate()
            .map(|(index, x)| {
                if let Some(sig) = x {
                    let mut temp = [0u8; 65];
                    if sig.len() == 65 {
                        temp.copy_from_slice(&*sig.encode());
                        Some(SignatureWithAuthorityIndex {
                            index: index as u32,
                            signature: temp,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .filter_map(|x| x)
            .collect::<Vec<_>>();

        let signature_indices = signatures
            .iter()
            .map(|x| x.index as usize)
            .collect::<Vec<_>>();

        let tree =
            rs_merkle::MerkleTree::<MerkleHasher<Crypto>>::from_leaves(&authority_address_hashes);

        let authority_proof = tree.proof(&signature_indices);

        MmrUpdateProof {
            signed_commitment: SignedCommitment {
                commitment: signed_commitment.commitment.clone(),
                signatures,
            },
            latest_mmr_leaf: latest_leaf.clone(),
            mmr_proof,
            authority_proof: authority_proof.proof_hashes().to_vec(),
        }
    }

    #[tokio::test]
    async fn test_continuous_update_of_beefy_client() {
        let client_id = ClientId::new(ClientType::Beefy, 0).unwrap();

        let chain_start_height = Height::new(1, 11);

        let mut ctx = MockContext::new(
            ChainId::new("mockgaiaA".to_string(), 1),
            HostType::Mock,
            5,
            chain_start_height,
        );

        let signer = get_dummy_account_id();

        let beefy_client_state = BeefyClientState {
            chain_id: Default::default(),
            frozen_height: None,
            latest_beefy_height: 0,
            mmr_root_hash: Default::default(),
            authority: BeefyNextAuthoritySet {
                id: 0,
                len: 5,
                root: H256::from(hex!(
                    "baa93c7834125ee3120bac6e3342bd3f28611110ad21ab6075367abdffefeb09"
                )),
            },
            next_authority_set: BeefyNextAuthoritySet {
                id: 1,
                len: 5,
                root: H256::from(hex!(
                    "baa93c7834125ee3120bac6e3342bd3f28611110ad21ab6075367abdffefeb09"
                )),
            },
            beefy_activation_block: 0,
        };

        let create_client = MsgCreateAnyClient {
            client_state: AnyClientState::Beefy(beefy_client_state),
            consensus_state: None,
            signer: signer.clone(),
        };

        // Create the client
        let res = dispatch::<_, Crypto>(&ctx, ClientMsg::CreateClient(create_client)).unwrap();
        ctx.store_client_result(res.result).unwrap();

        let url = std::env::var("NODE_ENDPOINT").unwrap_or("ws://127.0.0.1:9944".to_string());
        let client = subxt::ClientBuilder::new()
            .set_url(url)
            .build::<subxt::DefaultConfig>()
            .await
            .unwrap();
        let api =
        client.clone().to_runtime_api::<runtime::api::RuntimeApi<
            subxt::DefaultConfig,
            subxt::PolkadotExtrinsicParams<_>,
        >>();
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
        let mut count = 0;
        let client_state = ctx.client_state(&client_id).unwrap();
        // Before watching for commitments, we need to check that out initial validator set id is correct
        let next_val_set = api
            .storage()
            .mmr_leaf()
            .beefy_next_authorities(None)
            .await
            .unwrap();
        match client_state {
            AnyClientState::Tendermint(_) => {}
            AnyClientState::Beefy(mut client_state) => {
                if next_val_set.id != client_state.next_authority_set.id {
                    // Update the Id
                    // Note that the authorities are not changing, only the id is changing in this development scenario
                    client_state.next_authority_set.id = next_val_set.id;
                    client_state.authority.id = next_val_set.id - 1;
                    ctx.store_client_state(client_id.clone(), AnyClientState::Beefy(client_state))
                        .unwrap();
                }
            }
            AnyClientState::Mock(_) => {}
        }
        let mut latest_beefy_height = 0;

        while let Some(Ok(commitment)) = subscription.next().await {
            if count == 10 {
                break;
            }
            let recv_commitment: sp_core::Bytes =
                serde_json::from_value(JsonValue::String(commitment)).unwrap();
            let signed_commitment: beefy_primitives::SignedCommitment<
                u32,
                beefy_primitives::crypto::Signature,
            > = codec::Decode::decode(&mut &*recv_commitment).unwrap();

            std::println!(
                "Received signed commitmment for: {:?}",
                signed_commitment.commitment.block_number
            );

            let block_number = signed_commitment.commitment.block_number;
            let subxt_block_number: subxt::BlockNumber = block_number.into();
            let block_hash = client
                .rpc()
                .block_hash(Some(subxt_block_number))
                .await
                .unwrap();

            let para_ids = api.storage().paras().parachains(block_hash).await.unwrap();
            let storage_prefix = frame_support::storage::storage_prefix(b"Paras", b"Heads");
            let mut para_header_keys = Vec::new();

            for para_id in para_ids {
                let encoded_para_id = para_id.encode();

                let mut full_key = storage_prefix.clone().to_vec();
                full_key.extend_from_slice(sp_core::hashing::twox_64(&encoded_para_id).as_slice());
                full_key.extend_from_slice(&encoded_para_id);
                para_header_keys.push(subxt::sp_core::storage::StorageKey(full_key));
            }

            let previous_finalized_block_number: subxt::BlockNumber =
                (latest_beefy_height + 1).into();
            let previous_finalized_hash = client
                .rpc()
                .block_hash(Some(previous_finalized_block_number))
                .await
                .unwrap()
                .unwrap();

            let change_set = client
                .storage()
                .query_storage(para_header_keys, previous_finalized_hash, block_hash)
                .await
                .unwrap();
            let mut finalized_blocks = BTreeMap::new();
            let mut leaf_indices = vec![];
            for changes in change_set {
                let header = client
                    .rpc()
                    .header(Some(changes.block))
                    .await
                    .unwrap()
                    .unwrap();

                let mut heads = BTreeMap::new();

                for (key, value) in changes.changes {
                    if let Some(storage_data) = value {
                        let key = key.0.to_vec();
                        let para_id = u32::decode(&mut &key[40..]).unwrap();
                        let head_data: runtime::api::runtime_types::polkadot_parachain::primitives::HeadData = Decode::decode(&mut &*storage_data.0).unwrap();
                        heads.insert(para_id, head_data.0);
                    }
                }

                if !heads.contains_key(&PARA_ID) {
                    continue;
                }
                finalized_blocks.insert(header.number as u64, heads);
                leaf_indices.push(header.number - 1);
            }

            let batch_proof: pallet_mmr_rpc::LeafBatchProof<H256> = client
                .rpc()
                .client
                .request(
                    "mmr_generateBatchProof",
                    rpc_params!(leaf_indices.clone(), block_hash),
                )
                .await
                .unwrap();

            let leaves: Vec<Vec<u8>> = Decode::decode(&mut &*batch_proof.leaves.to_vec()).unwrap();

            let mut parachain_headers = vec![];
            for leaf_bytes in leaves {
                let leaf: MmrLeaf<u32, H256, H256, H256> =
                    Decode::decode(&mut &*leaf_bytes).unwrap();
                let leaf_block_number = (leaf.parent_number_and_hash.0 + 1) as u64;
                let para_headers = finalized_blocks.get(&leaf_block_number).unwrap();

                let mut index = None;
                let mut parachain_leaves = vec![];
                // Values are already sorted by key which is the para_id
                for (idx, (key, header)) in para_headers.iter().enumerate() {
                    let pair = (*key, header.clone());
                    let leaf_hash = keccak_256(pair.encode().as_slice());
                    parachain_leaves.push(leaf_hash);
                    if key == &PARA_ID {
                        index = Some(idx);
                    }
                }

                let tree =
                    rs_merkle::MerkleTree::<MerkleHasher<Crypto>>::from_leaves(&parachain_leaves);

                let proof = if let Some(index) = index {
                    tree.proof(&[index])
                        .proof_hashes()
                        .into_iter()
                        .map(|item| item.clone())
                        .collect::<Vec<_>>()
                } else {
                    vec![]
                };

                let header = ParachainHeader {
                    parachain_header: para_headers.get(&PARA_ID).unwrap().clone(),
                    partial_mmr_leaf: PartialMmrLeaf {
                        version: leaf.version,
                        parent_number_and_hash: leaf.parent_number_and_hash,
                        beefy_next_authority_set: leaf.beefy_next_authority_set.clone(),
                    },
                    para_id: PARA_ID,
                    parachain_heads_proof: proof,
                    heads_leaf_index: index.unwrap() as u32,
                    heads_total_count: parachain_leaves.len() as u32,
                    extrinsic_proof: vec![],
                };

                parachain_headers.push(header);
            }

            let batch_proof: pallet_mmr_primitives::BatchProof<H256> =
                codec::Decode::decode(&mut batch_proof.proof.0.as_slice()).unwrap();

            let mmr_update = get_mmr_update(&client, signed_commitment.clone()).await;

            let mmr_size = NodesUtils::new(batch_proof.leaf_count).size();

            let header = BeefyHeader {
                parachain_headers: parachain_headers
                    .into_iter()
                    .map(|header| BeefyParachainHeader {
                        parachain_header: Decode::decode(&mut &*header.parachain_header.as_slice())
                            .unwrap(),
                        partial_mmr_leaf: header.partial_mmr_leaf,
                        para_id: header.para_id,
                        parachain_heads_proof: header.parachain_heads_proof,
                        heads_leaf_index: header.heads_leaf_index,
                        heads_total_count: header.heads_total_count,
                        extrinsic_proof: header.extrinsic_proof,
                    })
                    .collect(),
                mmr_proofs: batch_proof
                    .items
                    .into_iter()
                    .map(|item| item.encode())
                    .collect(),
                mmr_size,
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

                    match result {
                        Update(upd_res) => {
                            assert_eq!(upd_res.client_id, client_id);
                            assert!(!upd_res.client_state.is_frozen());
                            assert_eq!(
                                upd_res.client_state,
                                ctx.latest_client_states(&client_id).clone()
                            );
                            assert_eq!(
                                upd_res.client_state.latest_height(),
                                Height::new(0, signed_commitment.commitment.block_number as u64),
                            )
                        }
                        _ => panic!("update handler result has incorrect type"),
                    }
                }
                Err(e) => panic!("Unexpected error {:?}", e),
            }
            latest_beefy_height = signed_commitment.commitment.block_number;
            count += 1;
        }
    }
}
