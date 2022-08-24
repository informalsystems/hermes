use core::fmt::{Display, Error as FmtError, Formatter};
use ibc_proto::cosmos::auth::v1beta1::BaseAccount;

/// Wrapper for account number and sequence number.
///
/// More fields may be added later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Account {
    pub address: AccountAddress,
    pub number: AccountNumber,
    pub sequence: AccountSequence,
    // pub pub_key: Option<prost_types::Any>,
}

impl From<BaseAccount> for Account {
    fn from(value: BaseAccount) -> Self {
        Self {
            address: AccountAddress::new(value.address),
            number: AccountNumber::new(value.account_number),
            sequence: AccountSequence::new(value.sequence),
        }
    }
}

/// Newtype for account address
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccountAddress(String);

impl AccountAddress {
    pub fn new(string: String) -> Self {
        Self(string)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }
}

impl Display for AccountAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.0)
    }
}

/// Newtype for account numbers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccountNumber(u64);

impl AccountNumber {
    pub fn new(number: u64) -> Self {
        Self(number)
    }

    pub fn to_u64(self) -> u64 {
        self.0
    }
}

impl Display for AccountNumber {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.0)
    }
}

/// Newtype for account sequence numbers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccountSequence(u64);

impl AccountSequence {
    pub fn new(sequence: u64) -> Self {
        Self(sequence)
    }

    pub fn to_u64(self) -> u64 {
        self.0
    }

    pub fn increment(self) -> Self {
        Self(self.0 + 1)
    }

    pub fn increment_mut(&mut self) {
        self.0 += 1
    }
}

impl Display for AccountSequence {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.0)
    }
}
