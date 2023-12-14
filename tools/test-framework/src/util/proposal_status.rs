use std::str::FromStr;

use serde_json::Value;

use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposalStatus {
    Unspecified = 0,
    DepositPeriod = 1,
    VotingPeriod = 2,
    Passed = 3,
    Rejected = 4,
    Failed = 5,
}

impl TryFrom<i64> for ProposalStatus {
    type Error = Error;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Unspecified),
            1 => Ok(Self::DepositPeriod),
            2 => Ok(Self::VotingPeriod),
            3 => Ok(Self::Passed),
            4 => Ok(Self::Rejected),
            5 => Ok(Self::Failed),
            _ => Err(Error::generic(eyre!(
                "unknown value for proposal status: `{value}`"
            ))),
        }
    }
}

impl FromStr for ProposalStatus {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "PROPOSAL_STATUS_UNSPECIFIED" => Ok(Self::Unspecified),
            "PROPOSAL_STATUS_DEPOSIT_PERIOD" => Ok(Self::DepositPeriod),
            "PROPOSAL_STATUS_VOTING_PERIOD" => Ok(Self::VotingPeriod),
            "PROPOSAL_STATUS_PASSED" => Ok(Self::Passed),
            "PROPOSAL_STATUS_REJECTED" => Ok(Self::Rejected),
            "PROPOSAL_STATUS_FAILED" => Ok(Self::Failed),
            _ => Err(Error::generic(eyre!(
                "unknown value for proposal status: `{s}`"
            ))),
        }
    }
}

impl ProposalStatus {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Unspecified => "PROPOSAL_STATUS_UNSPECIFIED",
            Self::DepositPeriod => "PROPOSAL_STATUS_DEPOSIT_PERIOD",
            Self::VotingPeriod => "PROPOSAL_STATUS_VOTING_PERIOD",
            Self::Passed => "PROPOSAL_STATUS_PASSED",
            Self::Rejected => "PROPOSAL_STATUS_REJECTED",
            Self::Failed => "PROPOSAL_STATUS_FAILED",
        }
    }
}

impl TryFrom<&Value> for ProposalStatus {
    type Error = Error;

    fn try_from(value: &Value) -> Result<Self, Self::Error> {
        if let Some(numeric_value) = value.as_i64() {
            ProposalStatus::try_from(numeric_value)
        } else {
            // If .to_string() is used directly on a serde_json::Value the double quotes are kept in the string.
            // Example: would result in `\"PROPOSAL_STATUS_VOTING_PERIOD\"` instead of `PROPOSAL_STATUS_VOTING_PERIOD`
            let str_value = value
                .as_str()
                .ok_or_else(|| eyre!("error converting value to str: `{value}`"))?;
            ProposalStatus::from_str(str_value)
        }
    }
}
