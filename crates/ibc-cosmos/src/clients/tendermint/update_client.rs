use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::core::traits::client::ContainsClient;
use ibc_framework::core::traits::error::{HasError, InjectError};
use ibc_framework::core::traits::handlers::update_client::UpdateClientHandler;
use ibc_framework::core::traits::host::HasHostMethods;
use ibc_framework::core::traits::ibc::HasIbcTypes;
use ibc_framework::core::traits::stores::client_reader::HasClientReader;
use tendermint::block::Height as BlockHeight;
use tendermint_light_client_verifier::errors::VerificationErrorDetail;
use tendermint_light_client_verifier::operations::voting_power::VotingPowerTally;
use tendermint_light_client_verifier::types::{TrustedBlockState, UntrustedBlockState};
use tendermint_light_client_verifier::{Verdict, Verifier};

use crate::clients::tendermint::client::{
    TendermintClient, TendermintClientHeader, TendermintClientState, TendermintConsensusState,
};

pub enum Error {
    MismatchRevision {
        current_revision: u64,
        update_revision: u64,
    },
    ConsensusStateNotFound {
        height: Height,
    },
    RevisionHeightOverflow {
        height: u64,
    },
    NotEnoughTrust {
        tally: VotingPowerTally,
    },
    VerificationError {
        detail: VerificationErrorDetail,
    },
    HeaderTimestampTooHigh {
        actual: Timestamp,
        max: Timestamp,
    },
    HeaderTimestampTooLow {
        actual: Timestamp,
        max: Timestamp,
    },
    InvalidHeight,
}

impl<Context> UpdateClientHandler<Context> for TendermintClient
where
    Context: HasError,
    Context: HasIbcTypes,
    Context: HasHostMethods<Height = Height, Timestamp = Timestamp>,
    Context: HasClientReader<TendermintClient>,
    Context: ContainsClient<TendermintClient>,
    Context: InjectError<Error>,
{
    type Client = TendermintClient;

    fn check_client_header_and_update_state(
        context: &Context,
        client_id: &Context::ClientId,
        client_state: &TendermintClientState,
        new_client_header: &TendermintClientHeader,
    ) -> Result<(TendermintClientState, TendermintConsensusState), Context::Error> {
        let new_height = new_client_header.height();

        let current_revision = client_state.chain_id.version();
        let update_revision = new_client_header.height().revision_number();

        if current_revision != update_revision {
            return Err(Context::inject_error(Error::MismatchRevision {
                current_revision,
                update_revision,
            }));
        }

        let new_consensus_state = TendermintConsensusState::from(new_client_header.clone());

        let m_current_client_consensus_state =
            context.get_consensus_state_at_height(client_id, &new_height)?;

        if m_current_client_consensus_state.as_ref() == Some(&new_consensus_state) {
            return Ok((client_state.clone(), new_consensus_state));
        }

        {
            let trusted_height = new_client_header.trusted_height;

            let trusted_consensus_state = context
                .get_consensus_state_at_height(client_id, &trusted_height)?
                .ok_or_else(|| {
                    Context::inject_error(Error::ConsensusStateNotFound {
                        height: trusted_height,
                    })
                })?;

            let trusted_revision_height = trusted_height.revision_height();

            let trusted_block_height =
                BlockHeight::try_from(trusted_revision_height).map_err(|_| {
                    Context::inject_error(Error::RevisionHeightOverflow {
                        height: trusted_revision_height,
                    })
                })?;

            let trusted_state = TrustedBlockState {
                header_time: trusted_consensus_state.timestamp,
                height: trusted_block_height,
                next_validators: &new_client_header.trusted_validator_set,
                next_validators_hash: trusted_consensus_state.next_validators_hash,
            };

            let untrusted_state = UntrustedBlockState {
                signed_header: &new_client_header.signed_header,
                validators: &new_client_header.validator_set,
                // NB: This will skip the
                // VerificationPredicates::next_validators_match check for the
                // untrusted state.
                next_validators: None,
            };

            let options = client_state.as_light_client_options().unwrap();

            let now = context.host_timestamp().into_tm_time().unwrap();

            let verdict =
                client_state
                    .verifier
                    .verify(untrusted_state, trusted_state, &options, now);

            match verdict {
                Verdict::Success => {}
                Verdict::NotEnoughTrust(voting_power_tally) => {
                    return Err(Context::inject_error(Error::NotEnoughTrust {
                        tally: voting_power_tally,
                    }));
                }
                Verdict::Invalid(detail) => {
                    return Err(Context::inject_error(Error::VerificationError { detail }))
                }
            }
        }

        // If the header has verified, but its corresponding consensus state
        // differs from the existing consensus state for that height, freeze the
        // client and return the installed consensus state.
        //
        // Note that this must be done *after* the light client verification.
        // So that invalid headers will result in verification errors instead
        // of errorneously freezing clients.
        if let Some(cs) = m_current_client_consensus_state {
            if cs != new_consensus_state {
                return Ok((
                    client_state
                        .clone()
                        .with_frozen_height(new_client_header.height()),
                    cs,
                ));
            }
        }

        // Monotonicity checks for timestamps for in-the-middle updates
        // (cs-new, cs-next, cs-latest)
        if new_client_header.height() < client_state.latest_height() {
            let m_next_consensus_state =
                context.get_consensus_state_after_height(client_id, &new_height)?;

            if let Some(next_cs) = m_next_consensus_state {
                // New (untrusted) header timestamp cannot occur after next
                // consensus state's height
                if new_client_header.signed_header.header().time > next_cs.timestamp {
                    return Err(Context::inject_error(Error::HeaderTimestampTooHigh {
                        actual: new_client_header.signed_header.header().time.into(),
                        max: next_cs.timestamp.into(),
                    }));
                }
            }
        }

        // (cs-trusted, cs-prev, cs-new)
        if new_client_header.trusted_height < new_client_header.height() {
            let m_prev_consensus_state =
                context.get_consensus_state_after_height(client_id, &new_height)?;

            if let Some(prev_cs) = m_prev_consensus_state {
                // New (untrusted) header timestamp cannot occur before the
                // previous consensus state's height
                if new_client_header.signed_header.header().time < prev_cs.timestamp {
                    return Err(Context::inject_error(Error::HeaderTimestampTooLow {
                        actual: new_client_header.signed_header.header().time.into(),
                        max: prev_cs.timestamp.into(),
                    }));
                }
            }
        }

        let latest_height = Height::new(
            client_state.latest_height.revision_number(),
            new_client_header.signed_header.header.height.into(),
        )
        .map_err(|_| Context::inject_error(Error::InvalidHeight))?;

        let mut new_client_state = client_state.clone();

        new_client_state.latest_height = latest_height;

        Ok((new_client_state, new_consensus_state))
    }
}
