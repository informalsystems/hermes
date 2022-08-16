use tendermint_testgen::light_block::TmLightBlock;

use ibc::clients::ics07_tendermint::header::Header as TmHeader;
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::mock::host::HostBlock;
use ibc::Height;

use crate::chain::mock::MockChain;
use crate::client_state::AnyClientState;
use crate::error::Error;
use crate::misbehaviour::MisbehaviourEvidence;

use super::Verified;
use ibc::timestamp::Timestamp;

/// A light client serving a mock chain.
pub struct LightClient {
    chain_id: ChainId,
}

impl LightClient {
    pub fn new(chain_id: ChainId) -> LightClient {
        LightClient { chain_id }
    }

    /// Returns a LightBlock at the requested height `h`.
    fn light_block(&self, h: Height) -> TmLightBlock {
        HostBlock::generate_tm_block(self.chain_id.clone(), h.revision_height(), Timestamp::now())
            .light_block
    }
}

impl super::LightClient<MockChain> for LightClient {
    fn verify(
        &mut self,
        _trusted: Height,
        target: Height,
        _client_state: &AnyClientState,
    ) -> Result<Verified<TmLightBlock>, Error> {
        Ok(Verified {
            target: self.light_block(target),
            supporting: Vec::new(),
        })
    }

    fn fetch(&mut self, height: Height) -> Result<TmLightBlock, Error> {
        Ok(self.light_block(height))
    }

    fn check_misbehaviour(
        &mut self,
        _update: &UpdateClient,
        _client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        unimplemented!()
    }

    fn header_and_minimal_set(
        &mut self,
        trusted_height: Height,
        target_height: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<TmHeader>, Error> {
        let Verified { target, supporting } =
            self.verify(trusted_height, target_height, client_state)?;

        assert!(supporting.is_empty());

        let succ_trusted = self.fetch(trusted_height.increment())?;

        let target = TmHeader {
            signed_header: target.signed_header,
            validator_set: target.validators,
            trusted_height,
            trusted_validator_set: succ_trusted.validators,
        };

        Ok(Verified {
            target,
            supporting: Vec::new(),
        })
    }
}
