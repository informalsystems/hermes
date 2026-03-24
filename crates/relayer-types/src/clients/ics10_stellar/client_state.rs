use std::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::clients::ics10_stellar::error::Error;
use crate::clients::ics10_stellar::raw::{RawClientState, STELLAR_CLIENT_STATE_TYPE_URL};
use crate::core::ics02_client::client_state::ClientState as Ics2ClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics24_host::identifier::ChainId;
use crate::Height;

/// Stellar IBC light client state.
///
/// Tracks a Stellar network's consensus from the perspective of a counterpart
/// IBC-enabled chain. Verification relies on SCP consensus proofs (quorum of
/// EXTERNALIZE envelopes) rather than Merkle inclusion proofs.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClientState {
    /// Chain identifier of the tracked Stellar network
    pub chain_id: ChainId,
    /// Height of the most recent trusted ledger
    pub latest_height: Height,
    /// How long headers are trusted after the ledger close time
    pub trusting_period: Duration,
    /// Unbonding period of the Stellar network
    pub unbonding_period: Duration,
    /// Set to a non-zero height if the client has been frozen due to misbehaviour
    pub frozen_height: Option<Height>,
}

impl ClientState {
    pub fn new(
        chain_id: ChainId,
        latest_height: Height,
        trusting_period: Duration,
        unbonding_period: Duration,
    ) -> Self {
        Self {
            chain_id,
            latest_height,
            trusting_period,
            unbonding_period,
            frozen_height: None,
        }
    }
}

impl Ics2ClientState for ClientState {
    fn chain_id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Stellar
    }

    fn latest_height(&self) -> Height {
        self.latest_height
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height
    }

    fn expired(&self, elapsed: Duration) -> bool {
        elapsed > self.trusting_period
    }
}

// ---------------------------------------------------------------------------
// Protobuf conversions
// ---------------------------------------------------------------------------

impl Protobuf<RawClientState> for ClientState {}

impl TryFrom<RawClientState> for ClientState {
    type Error = Error;

    fn try_from(raw: RawClientState) -> Result<Self, Self::Error> {
        let chain_id = ChainId::from_string(&raw.chain_id);

        let latest_height: Height = raw
            .latest_height
            .ok_or_else(|| Error::invalid_raw_client_state("missing latest_height".into()))?
            .try_into()
            .map_err(|_| Error::invalid_raw_client_state("invalid latest_height".into()))?;

        let trusting_period = Duration::from_nanos(raw.trusting_period_ns);
        let unbonding_period = Duration::from_nanos(raw.unbonding_period_ns);

        let frozen_height = raw
            .frozen_height
            .map(|h| h.try_into())
            .transpose()
            .map_err(|_| Error::invalid_raw_client_state("invalid frozen_height".into()))?;

        Ok(Self {
            chain_id,
            latest_height,
            trusting_period,
            unbonding_period,
            frozen_height,
        })
    }
}

impl From<ClientState> for RawClientState {
    fn from(value: ClientState) -> Self {
        Self {
            chain_id: value.chain_id.to_string(),
            latest_height: Some(value.latest_height.into()),
            trusting_period_ns: value.trusting_period.as_nanos() as u64,
            unbonding_period_ns: value.unbonding_period.as_nanos() as u64,
            frozen_height: value.frozen_height.map(Into::into),
        }
    }
}

impl Protobuf<Any> for ClientState {}

impl TryFrom<Any> for ClientState {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            STELLAR_CLIENT_STATE_TYPE_URL => RawClientState::decode(raw.value.as_ref())
                .map_err(|e| Error::decode(e.into()))?
                .try_into()
                .map_err(Into::into),
            _ => Err(Ics02Error::unknown_client_state_type(raw.type_url)),
        }
    }
}

impl From<ClientState> for Any {
    fn from(value: ClientState) -> Self {
        Any {
            type_url: STELLAR_CLIENT_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawClientState>::encode_vec(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use std::time::Duration;

    use ibc_proto::google::protobuf::Any;

    use super::ClientState;
    use crate::clients::ics10_stellar::raw::STELLAR_CLIENT_STATE_TYPE_URL;
    use crate::core::ics02_client::client_state::ClientState as Ics2ClientState;
    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics24_host::identifier::ChainId;
    use crate::Height;

    fn sample_client_state() -> ClientState {
        ClientState::new(
            ChainId::from_string("stellar-testnet-1"),
            Height::new(0, 5000).unwrap(),
            Duration::from_secs(7 * 24 * 3600), // 1 week trusting period
            Duration::from_secs(14 * 24 * 3600), // 2 week unbonding period
        )
    }

    #[test]
    fn client_type_is_stellar() {
        assert_eq!(sample_client_state().client_type(), ClientType::Stellar);
    }

    #[test]
    fn accessors() {
        let cs = sample_client_state();
        assert_eq!(cs.chain_id(), ChainId::from_string("stellar-testnet-1"));
        assert_eq!(cs.latest_height(), Height::new(0, 5000).unwrap());
        assert!(!cs.is_frozen());
        assert_eq!(cs.frozen_height(), None);
    }

    #[test]
    fn expired_within_trusting_period() {
        let cs = sample_client_state();
        assert!(!cs.expired(Duration::from_secs(3 * 24 * 3600))); // 3 days — still valid
    }

    #[test]
    fn expired_beyond_trusting_period() {
        let cs = sample_client_state();
        assert!(cs.expired(Duration::from_secs(8 * 24 * 3600))); // 8 days — expired
    }

    #[test]
    fn frozen_height_marks_client_frozen() {
        let mut cs = sample_client_state();
        cs.frozen_height = Some(Height::new(0, 100).unwrap());
        assert!(cs.is_frozen());
        assert_eq!(cs.frozen_height(), Some(Height::new(0, 100).unwrap()));
    }

    #[test]
    fn roundtrip_raw() {
        use crate::clients::ics10_stellar::raw::RawClientState;

        let original = sample_client_state();
        let raw = RawClientState::from(original.clone());
        let recovered = ClientState::try_from(raw).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any() {
        let original = sample_client_state();
        let any = Any::from(original.clone());
        assert_eq!(any.type_url, STELLAR_CLIENT_STATE_TYPE_URL);
        let recovered = ClientState::try_from(any).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any_with_frozen_height() {
        let mut original = sample_client_state();
        original.frozen_height = Some(Height::new(0, 42).unwrap());
        let any = Any::from(original.clone());
        let recovered = ClientState::try_from(any).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn missing_latest_height_returns_error() {
        use crate::clients::ics10_stellar::raw::RawClientState;

        let raw = RawClientState {
            chain_id: "stellar-testnet-1".to_string(),
            latest_height: None,
            trusting_period_ns: 1_000_000,
            unbonding_period_ns: 2_000_000,
            frozen_height: None,
        };
        assert!(ClientState::try_from(raw).is_err());
    }

    #[test]
    fn unknown_type_url_returns_error() {
        let any = Any {
            type_url: "/some.other.ClientState".to_string(),
            value: vec![],
        };
        assert!(ClientState::try_from(any).is_err());
    }
}
