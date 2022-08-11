use crate::prelude::*;
use beefy_primitives::known_payload_ids::MMR_ROOT_ID;
use beefy_primitives::mmr::BeefyNextAuthoritySet;
use codec::{Decode, Encode};
use core::convert::TryFrom;
use core::fmt;
use core::str::FromStr;
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
    /// Relay chain
    pub relay_chain: RelayChain,
    /// Latest mmr root hash
    pub mmr_root_hash: H256,
    /// block number for the latest mmr_root_hash
    pub latest_beefy_height: u32,
    /// Block height when the client was frozen due to a misbehaviour
    pub frozen_height: Option<Height>,
    /// Block number that the beefy protocol was activated on the relay chain.
    /// This should be the first block in the merkle-mountain-range tree.
    pub beefy_activation_block: u32,
    /// latest parachain height
    pub latest_para_height: u32,
    /// ParaId of associated parachain
    pub para_id: u32,
    /// authorities for the current round
    pub authority: BeefyNextAuthoritySet<H256>,
    /// authorities for the next round
    pub next_authority_set: BeefyNextAuthoritySet<H256>,
}

impl Protobuf<RawClientState> for ClientState {}

impl ClientState {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        relay_chain: RelayChain,
        para_id: u32,
        latest_para_height: u32,
        mmr_root_hash: H256,
        beefy_activation_block: u32,
        latest_beefy_height: u32,
        authority_set: BeefyNextAuthoritySet<H256>,
        next_authority_set: BeefyNextAuthoritySet<H256>,
    ) -> Result<ClientState, Error> {
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
        let chain_id = ChainId::new(relay_chain.to_string(), para_id.into());

        Ok(Self {
            chain_id,
            mmr_root_hash,
            latest_beefy_height,
            frozen_height: None,
            beefy_activation_block,
            authority: authority_set,
            next_authority_set,
            relay_chain,
            latest_para_height,
            para_id,
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
        let latest_para_height = Height::new(self.para_id.into(), self.latest_para_height.into());
        if latest_para_height < height {
            return Err(Error::insufficient_height(latest_para_height, height));
        }

        match self.frozen_height {
            Some(frozen_height) if frozen_height <= height => {
                Err(Error::client_frozen(frozen_height, height))
            }
            _ => Ok(()),
        }
    }

    /// Check if the state is expired when `elapsed` time has passed since the latest consensus
    /// state timestamp
    pub fn expired(&self, elapsed: Duration) -> bool {
        elapsed > self.relay_chain.trusting_period()
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
        Height::new(self.para_id.into(), self.latest_para_height.into())
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
        let relay_chain = RelayChain::from_i32(raw.relay_chain)?;
        let chain_id = ChainId::new(relay_chain.to_string(), raw.para_id.into());

        Ok(Self {
            chain_id,
            mmr_root_hash,
            latest_beefy_height: raw.latest_beefy_height,
            frozen_height,
            beefy_activation_block: raw.beefy_activation_block,
            authority: authority_set,
            next_authority_set,
            relay_chain,
            latest_para_height: raw.latest_para_height,
            para_id: raw.para_id,
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
            relay_chain: client_state.relay_chain as i32,
            para_id: client_state.para_id,
            latest_para_height: client_state.latest_para_height,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum RelayChain {
    Polkadot = 0,
    Kusama = 1,
    Rococo = 2,
}

impl Default for RelayChain {
    fn default() -> Self {
        RelayChain::Rococo
    }
}

impl fmt::Display for RelayChain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

// Unbonding period for relay chains in days
const POLKADOT_UNBONDING_PERIOD: u64 = 28;
const KUSAMA_UNBONDING_PERIOD: u64 = 7;

impl RelayChain {
    /// Yields the Order as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Polkadot => "Polkadot",
            Self::Kusama => "Kusama",
            Self::Rococo => "Rococo",
        }
    }

    // Parses the Order out from a i32.
    pub fn from_i32(nr: i32) -> Result<Self, Error> {
        match nr {
            0 => Ok(Self::Polkadot),
            1 => Ok(Self::Kusama),
            2 => Ok(Self::Rococo),
            id => Err(Error::unknown_relay_chain(id.to_string())),
        }
    }

    pub fn unbonding_period(&self) -> Duration {
        match self {
            Self::Polkadot => {
                let secs = POLKADOT_UNBONDING_PERIOD * 24 * 60 * 60;
                Duration::from_secs(secs)
            }
            Self::Kusama | Self::Rococo => {
                let secs = KUSAMA_UNBONDING_PERIOD * 24 * 60 * 60;
                Duration::from_secs(secs)
            }
        }
    }

    pub fn trusting_period(&self) -> Duration {
        let unbonding_period = self.unbonding_period();
        // Trusting period is 1/3 of unbonding period
        unbonding_period.checked_div(3).unwrap()
    }
}

impl FromStr for RelayChain {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().trim_start_matches("order_") {
            "polkadot" => Ok(Self::Polkadot),
            "kusama" => Ok(Self::Kusama),
            "rococo" => Ok(Self::Rococo),
            _ => Err(Error::unknown_relay_chain(s.to_string())),
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
                RelayChain::Rococo,
                2000,
                0,
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
