use crate::prelude::*;

use beefy_primitives::mmr::BeefyNextAuthoritySet;
use codec::{Decode, Encode};
use core::convert::TryFrom;
use primitive_types::H256;
use sp_runtime::SaturatedConversion;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::lightclients::beefy::v1::{BeefyAuthoritySet, ClientState as RawClientState};

use crate::clients::ics11_beefy::error::Error;
use crate::clients::ics11_beefy::header::BeefyHeader;
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics24_host::identifier::ChainId;
use crate::Height;

pub const REVISION_NUMBER: u64 = 0;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClientState {
    /// Latest mmr root hash
    pub mmr_root_hash: H256,
    /// block number for the latest mmr_root_hash
    pub latest_beefy_height: Height,
    /// Block height when the client was frozen due to a misbehaviour
    pub frozen_height: Option<Height>,
    /// block number that the beefy protocol was activated on the relay chain.
    /// This shoould be the first block in the merkle-mountain-range tree.
    pub beefy_activation_block: u32,
    /// authorities for the current round
    pub authority: BeefyNextAuthoritySet<H256>,
    /// authorities for the next round
    pub next_authority_set: BeefyNextAuthoritySet<H256>,
    /// Latest parachain height
    pub latest_parachain_height: Option<Height>,
}

impl Protobuf<RawClientState> for ClientState {}

impl ClientState {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        mmr_root_hash: H256,
        beefy_activation_block: u32,
        latest_beefy_height: u32,
        authority_set: BeefyNextAuthoritySet<H256>,
        next_authority_set: BeefyNextAuthoritySet<H256>,
    ) -> Result<ClientState, Error> {
        // Basic validation for the latest beefy height parameter.
        if latest_beefy_height < 0 {
            return Err(Error::validation(
                "ClientState latest beefy height must be greater than or equal to zero".to_string(),
            ));
        }

        Ok(Self {
            mmr_root_hash,
            latest_beefy_height: Height::new(REVISION_NUMBER, latest_beefy_height.into()),
            frozen_height: None,
            beefy_activation_block,
            authority: authority_set,
            next_authority_set,
            latest_parachain_height: None,
        })
    }

    pub fn latest_beefy_height(&self) -> Height {
        self.latest_beefy_height
    }

    pub fn latest_para_height(&self) -> Height {
        self.latest_parachain_height.unwrap_or_default()
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
        if self.latest_beefy_height < height {
            return Err(Error::insufficient_height(
                self.latest_beefy_height(),
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
        Default::default()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Beefy
    }

    fn latest_height(&self) -> Height {
        self.latest_para_height()
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height
    }

    fn upgrade(
        mut self,
        upgrade_height: Height,
        upgrade_options: UpgradeOptions,
        _chain_id: ChainId,
    ) -> Self {
        self.frozen_height = None;
        // Upgrade the client state
        self.latest_beefy_height = upgrade_height;

        self
    }

    fn wrap_any(self) -> AnyClientState {
        AnyClientState::Beefy(self)
    }
}

impl TryFrom<RawClientState> for ClientState {
    type Error = Error;

    fn try_from(raw: RawClientState) -> Result<Self, Self::Error> {
        let frozen_height = Some(Height::new(REVISION_NUMBER, raw.frozen_height));
        let latest_beefy_height = Height::new(REVISION_NUMBER, raw.latest_beefy_height.into());

        let authority_set = raw
            .authority
            .and_then(|set| {
                Some(BeefyNextAuthoritySet {
                    id: set.id,
                    len: set.len,
                    root: H256::decode(&mut &set.authority_root).ok()?,
                })
            })
            .ok_or(Error::missing_validator_set())?;

        let next_authority_set = raw
            .next_authority_set
            .and_then(|set| {
                Some(BeefyNextAuthoritySet {
                    id: set.id,
                    len: set.len,
                    root: H256::decode(&mut &set.authority_root).ok()?,
                })
            })
            .ok_or(Error::missing_validator_set())?;

        let mmr_root_hash = H256::decode(&mut &raw.mmr_root_hash).map_err(|_| Error::decode())?;

        Ok(Self {
            mmr_root_hash,
            latest_beefy_height,
            frozen_height,
            beefy_activation_block: raw.beefy_activation_block,
            authority: authority_set,
            next_authority_set,
            latest_parachain_height: None,
        })
    }
}

impl From<ClientState> for RawClientState {
    fn from(client_state: ClientState) -> Self {
        RawClientState {
            mmr_root_hash: client_state.mmr_root_hash.encode(),
            latest_beefy_height: client_state
                .latest_beefy_height
                .revision_height
                .saturated_into::<u32>(),
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

#[cfg(test)]
mod tests {
    #[test]
    fn client_state_new() {}

    #[test]
    fn client_state_verify_delay_passed() {}

    #[test]
    fn client_state_verify_height() {}
}
