//! IBC Domain type definition for [`TrustThreshold`]
//! represented as a fraction with valid values in the
//! range `[0, 1)`.

use core::convert::TryFrom;
use core::fmt::{Display, Error as FmtError, Formatter};

use ibc_proto::protobuf::Protobuf;
use num_rational::Ratio;
use serde::{Deserialize, Serialize};

use ibc_proto::ibc::lightclients::tendermint::v1::Fraction;
use tendermint::trust_threshold::TrustThresholdFraction;

use crate::core::ics02_client::error::Error;

/// Represents the level of trust that a client has towards a set of validators
/// of a chain. Another way to phrase it is that the trust threshold defines
/// the minimum amount of voting power in a block that originates from trusted
/// validators.
///
/// To be a bit more concrete, given a _trusted_ header at height H1 and an
/// _untrusted_ header at height H2 with H2 > H1, of the set of validators for
/// the block at height H2 proposed by the validators of the block at height H1,
/// the trust threshold specifies the minimal ratio of voting power that must
/// originate from the trusted validators at height H1 in order to deem the
/// block at height H2 as trusted.
///
/// Since Tendermint assumes that at least 2/3 validators are trustworthy, then
/// if at least 1/3 of the voting power in block H2 originates from the trusted
/// validators at height H1, then at least 1 trusted validator proposed the
/// block at height H2. Thus, a typical trust threshold in practice is 1/3.
///
/// This type accepts even a value of 0, (numerator = 0, denominator = 0),
/// which is used in the client state of an upgrading client.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TrustThreshold(Ratio<u64>);

impl TrustThreshold {
    /// Constant for a trust threshold of 1/3.
    pub const ONE_THIRD: Self = Self(Ratio::new_raw(1, 3));

    /// Constant for a trust threshold of 2/3.
    pub const TWO_THIRDS: Self = Self(Ratio::new_raw(2, 3));

    /// Constant for a trust threshold of 0/0.
    ///
    /// IMPORTANT: Only to be used for resetting the client state
    /// during a client upgrade. Using this value anywhere else
    /// might lead to panics.
    pub const CLIENT_STATE_RESET: Self = Self(Ratio::new_raw(0, 0));

    /// Instantiate a TrustThreshold with the given denominator and
    /// numerator.
    ///
    /// The constructor succeeds as long as the resulting fraction
    /// is a rational number in the range`[0, 1)`.
    pub fn new(numerator: u64, denominator: u64) -> Result<Self, Error> {
        // The fraction cannot be bigger than 1, nor can the denominator be zero
        if numerator > denominator || denominator == 0 {
            return Err(Error::invalid_trust_threshold(numerator, denominator));
        }

        Ok(Self(Ratio::new(numerator, denominator)))
    }

    /// The numerator of the fraction underlying this trust threshold.
    pub fn numerator(&self) -> u64 {
        *self.0.numer()
    }

    /// The denominator of the fraction underlying this trust threshold.
    pub fn denominator(&self) -> u64 {
        *self.0.denom()
    }
}

/// Conversion from Tendermint domain type into
/// IBC domain type.
impl From<TrustThresholdFraction> for TrustThreshold {
    fn from(t: TrustThresholdFraction) -> Self {
        Self(Ratio::new_raw(t.numerator(), t.denominator()))
    }
}

/// Conversion from IBC domain type into
/// Tendermint domain type.
impl TryFrom<TrustThreshold> for TrustThresholdFraction {
    type Error = Error;

    fn try_from(t: TrustThreshold) -> Result<TrustThresholdFraction, Error> {
        TrustThresholdFraction::new(t.numerator(), t.denominator())
            .map_err(|_| Error::failed_trust_threshold_conversion(t.numerator(), t.denominator()))
    }
}

impl Protobuf<Fraction> for TrustThreshold {}

impl From<TrustThreshold> for Fraction {
    fn from(t: TrustThreshold) -> Self {
        Fraction {
            numerator: t.numerator(),
            denominator: t.denominator(),
        }
    }
}

impl TryFrom<Fraction> for TrustThreshold {
    type Error = Error;

    fn try_from(value: Fraction) -> Result<Self, Self::Error> {
        Self::new(value.numerator, value.denominator)
    }
}

impl Default for TrustThreshold {
    fn default() -> Self {
        Self::ONE_THIRD
    }
}

impl Display for TrustThreshold {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}/{}", self.numerator(), self.denominator())
    }
}

impl Serialize for TrustThreshold {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        #[derive(Serialize)]
        struct TrustThreshold {
            numerator: u64,
            denominator: u64,
        }

        let tt = TrustThreshold {
            numerator: self.numerator(),
            denominator: self.denominator(),
        };

        tt.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TrustThreshold {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct TrustThreshold {
            numerator: u64,
            denominator: u64,
        }

        let tt = TrustThreshold::deserialize(deserializer)?;
        Self::new(tt.numerator, tt.denominator).map_err(serde::de::Error::custom)
    }
}
