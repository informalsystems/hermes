//! Extension events specific to chains followed via Cosmos SDK.

use serde_derive::Serialize;

use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use ibc::Height;

// Event type strings
const SUBMIT_PROPOSAL_EVENT: &str = "submit_proposal";

/// Variants that encode the possible message types sent via Cosmos SDK modules
#[derive(Debug, Serialize)]
pub enum CosmosEvent {
    SubmitProposal(SubmitProposal),

    ChainError(String), // Special event, signifying an error on CheckTx or DeliverTx
}

impl CosmosEvent {
    pub fn try_from_tx_response(height: Height, event: &AbciEvent) -> Option<CosmosEvent> {
        match &event.type_str[..] {
            SUBMIT_PROPOSAL_EVENT => {
                SubmitProposal::try_from_height_event_tags(height, &event.attributes)
                    .map(CosmosEvent::SubmitProposal)
            }
            _ => None,
        }
    }
}

/// Data of a "submit_proposal" event carrying a "proposal_id" tag.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SubmitProposal {
    pub proposal_id: u64,
    pub height: Height,
}

impl SubmitProposal {
    fn try_from_height_event_tags(height: Height, tags: &[Tag]) -> Option<Self> {
        let mut proposal_id = None;
        for tag in tags {
            let key = tag.key.as_ref();
            let value = tag.value.as_ref();
            if key == "proposal_id" {
                proposal_id = Some(value.parse().ok()?);
            } else {
                continue;
            }
        }
        let proposal_id = proposal_id?;
        Some(Self {
            height,
            proposal_id,
        })
    }
}
