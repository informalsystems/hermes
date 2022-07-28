use crate::prelude::*;

use beefy_primitives::known_payload_ids::MMR_ROOT_ID;
use beefy_primitives::mmr::BeefyNextAuthoritySet;
use codec::{Decode, Encode};
use core::convert::TryFrom;
use core::time::Duration;
use serde::{Deserialize, Serialize};
use sp_core::H256;
use sp_runtime::SaturatedConversion;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::lightclients::beefy::v1::{BeefyAuthoritySet, ClientState as RawClientState};

use crate::clients::ics11_beefy::error::Error;
use crate::clients::ics11_beefy::header::BeefyHeader;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics24_host::identifier::ChainId;
use crate::timestamp::Timestamp;
use crate::Height;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClientState {
    /// The chain id
    pub chain_id: ChainId,
    /// Latest mmr root hash
    pub mmr_root_hash: H256,
    /// block number for the latest mmr_root_hash
    pub latest_beefy_height: u32,
    /// Block height when the client was frozen due to a misbehaviour
    pub frozen_height: Option<Height>,
    /// Block number that the beefy protocol was activated on the relay chain.
    /// This should be the first block in the merkle-mountain-range tree.
    pub beefy_activation_block: u32,
    /// authorities for the current round
    pub authority: BeefyNextAuthoritySet<H256>,
    /// authorities for the next round
    pub next_authority_set: BeefyNextAuthoritySet<H256>,
}

impl Protobuf<RawClientState> for ClientState {}

impl ClientState {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        chain_id: ChainId,
        mmr_root_hash: H256,
        beefy_activation_block: u32,
        latest_beefy_height: u32,
        authority_set: BeefyNextAuthoritySet<H256>,
        next_authority_set: BeefyNextAuthoritySet<H256>,
    ) -> Result<ClientState, Error> {
        if chain_id.version() == 0 {
            return Err(Error::validation(
                "ClientState Chain id cannot be equal to zero ".to_string(),
            ));
        }

        if beefy_activation_block > latest_beefy_height {
            return Err(Error::validation(
                "ClientState beefy activation block cannot be greater than latest_beefy_height"
                    .to_string(),
            ));
        }

        if authority_set.id >= next_authority_set.id {
            return Err(Error::validation(
                "ClientState next authority set id must be greater than current authority set id"
                    .to_string(),
            ));
        }

        Ok(Self {
            chain_id,
            mmr_root_hash,
            latest_beefy_height,
            frozen_height: None,
            beefy_activation_block,
            authority: authority_set,
            next_authority_set,
        })
    }

    pub fn to_leaf_index(&self, block_number: u32) -> u32 {
        if self.beefy_activation_block == 0 {
            return block_number.saturating_sub(1);
        }
        self.beefy_activation_block.saturating_sub(block_number + 1)
    }

    /// Should only be called if this header has been verified successfully
    pub fn from_header(self, header: BeefyHeader) -> Result<Self, Error> {
        let mut clone = self.clone();
        let mut authority_changed = false;
        let (mmr_root_hash, latest_beefy_height, next_authority_set) =
            if let Some(mmr_update) = header.mmr_update_proof {
                if mmr_update.signed_commitment.commitment.validator_set_id
                    == self.next_authority_set.id
                {
                    authority_changed = true;
                }
                (
                    H256::from_slice(
                        mmr_update
                            .signed_commitment
                            .commitment
                            .payload
                            .get_raw(&MMR_ROOT_ID)
                            .ok_or_else(Error::invalid_raw_header)?,
                    ),
                    mmr_update.signed_commitment.commitment.block_number,
                    mmr_update.latest_mmr_leaf.beefy_next_authority_set,
                )
            } else {
                (
                    self.mmr_root_hash,
                    self.latest_beefy_height,
                    self.next_authority_set,
                )
            };
        clone.mmr_root_hash = mmr_root_hash;
        clone.latest_beefy_height = latest_beefy_height;
        if authority_changed {
            clone.authority = clone.next_authority_set;
            clone.next_authority_set = next_authority_set;
        }
        Ok(clone)
    }

    /// Verify the time and height delays
    pub fn verify_delay_passed(
        current_time: Timestamp,
        current_height: Height,
        processed_time: Timestamp,
        processed_height: Height,
        delay_period_time: Duration,
        delay_period_blocks: u64,
    ) -> Result<(), Error> {
        let earliest_time =
            (processed_time + delay_period_time).map_err(Error::timestamp_overflow)?;
        if !(current_time == earliest_time || current_time.after(&earliest_time)) {
            return Err(Error::not_enough_time_elapsed(current_time, earliest_time));
        }

        let earliest_height = processed_height.add(delay_period_blocks);
        if current_height < earliest_height {
            return Err(Error::not_enough_blocks_elapsed(
                current_height,
                earliest_height,
            ));
        }

        Ok(())
    }

    pub fn with_frozen_height(self, h: Height) -> Result<Self, Error> {
        if h == Height::zero() {
            return Err(Error::validation(
                "ClientState frozen height must be greater than zero".to_string(),
            ));
        }
        Ok(Self {
            frozen_height: Some(h),
            ..self
        })
    }

    /// Verify that the client is at a sufficient height and unfrozen at the given height
    pub fn verify_height(&self, height: Height) -> Result<(), Error> {
        if (self.latest_beefy_height as u64) < height.revision_height {
            return Err(Error::insufficient_height(
                Height::new(0, self.latest_beefy_height.into()),
                height,
            ));
        }

        match self.frozen_height {
            Some(frozen_height) if frozen_height <= height => {
                Err(Error::client_frozen(frozen_height, height))
            }
            _ => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UpgradeOptions;

impl crate::core::ics02_client::client_state::ClientState for ClientState {
    type UpgradeOptions = UpgradeOptions;

    fn chain_id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Beefy
    }

    fn latest_height(&self) -> Height {
        Height::new(0, self.latest_beefy_height.into())
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height
    }

    fn upgrade(
        mut self,
        upgrade_height: Height,
        _upgrade_options: UpgradeOptions,
        _chain_id: ChainId,
    ) -> Self {
        self.frozen_height = None;
        // Upgrade the client state
        self.latest_beefy_height = upgrade_height.revision_height.saturated_into::<u32>();

        self
    }

    fn wrap_any(self) -> AnyClientState {
        AnyClientState::Beefy(self)
    }
}

impl TryFrom<RawClientState> for ClientState {
    type Error = Error;

    fn try_from(raw: RawClientState) -> Result<Self, Self::Error> {
        let frozen_height = {
            let height = Height::new(0, raw.frozen_height.into());
            if height == Height::zero() {
                None
            } else {
                Some(height)
            }
        };

        let authority_set = raw
            .authority
            .and_then(|set| {
                Some(BeefyNextAuthoritySet {
                    id: set.id,
                    len: set.len,
                    root: H256::decode(&mut &*set.authority_root).ok()?,
                })
            })
            .ok_or_else(Error::missing_beefy_authority_set)?;

        let next_authority_set = raw
            .next_authority_set
            .and_then(|set| {
                Some(BeefyNextAuthoritySet {
                    id: set.id,
                    len: set.len,
                    root: H256::decode(&mut &*set.authority_root).ok()?,
                })
            })
            .ok_or_else(Error::missing_beefy_authority_set)?;

        let mmr_root_hash = H256::decode(&mut &*raw.mmr_root_hash).map_err(Error::scale_decode)?;

        Ok(Self {
            chain_id: ChainId::default(),
            mmr_root_hash,
            latest_beefy_height: raw.latest_beefy_height,
            frozen_height,
            beefy_activation_block: raw.beefy_activation_block,
            authority: authority_set,
            next_authority_set,
        })
    }
}

impl From<ClientState> for RawClientState {
    fn from(client_state: ClientState) -> Self {
        RawClientState {
            mmr_root_hash: client_state.mmr_root_hash.encode(),
            latest_beefy_height: client_state.latest_beefy_height,
            frozen_height: client_state
                .frozen_height
                .unwrap_or_default()
                .revision_height,
            beefy_activation_block: client_state.beefy_activation_block,
            authority: Some(BeefyAuthoritySet {
                id: client_state.authority.id,
                len: client_state.authority.len,
                authority_root: client_state.authority.root.encode(),
            }),
            next_authority_set: Some(BeefyAuthoritySet {
                id: client_state.next_authority_set.id,
                len: client_state.next_authority_set.len,
                authority_root: client_state.next_authority_set.root.encode(),
            }),
        }
    }
}

#[cfg(any(test, feature = "mocks"))]
pub mod test_util {
    use super::*;
    use crate::core::ics02_client::client_state::AnyClientState;

    pub fn get_dummy_beefy_state() -> AnyClientState {
        AnyClientState::Beefy(
            ClientState::new(
                ChainId::new("polkadot".to_string(), 1),
                Default::default(),
                0,
                0,
                Default::default(),
                Default::default(),
            )
            .unwrap(),
        )
    }
}
