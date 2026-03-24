use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::clients::ics10_stellar::error::Error;
use crate::clients::ics10_stellar::header::Header;
use crate::clients::ics10_stellar::raw::{RawMisbehaviour, STELLAR_MISBEHAVIOUR_TYPE_URL};
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics02_client::misbehaviour::Misbehaviour as Ics2Misbehaviour;
use crate::core::ics24_host::identifier::ClientId;
use crate::Height;

/// Stellar IBC light client misbehaviour.
///
/// Two headers at the same height with different ledger hashes constitute
/// evidence that a set of Stellar validators signed conflicting ledgers —
/// the on-chain light client can be frozen upon submission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Misbehaviour {
    pub client_id: ClientId,
    pub header1: Header,
    pub header2: Header,
}

impl Misbehaviour {
    pub fn new(client_id: ClientId, header1: Header, header2: Header) -> Self {
        Self {
            client_id,
            header1,
            header2,
        }
    }
}

impl Ics2Misbehaviour for Misbehaviour {
    fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    fn height(&self) -> Height {
        self.header1.height
    }
}

impl core::fmt::Display for Misbehaviour {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "StellarMisbehaviour {{ client_id: {}, h1: {}, h2: {} }}",
            self.client_id, self.header1, self.header2,
        )
    }
}

// ---------------------------------------------------------------------------
// Protobuf conversions
// ---------------------------------------------------------------------------

impl Protobuf<RawMisbehaviour> for Misbehaviour {}

impl TryFrom<RawMisbehaviour> for Misbehaviour {
    type Error = Error;

    fn try_from(raw: RawMisbehaviour) -> Result<Self, Self::Error> {
        let client_id = raw
            .client_id
            .parse()
            .map_err(|_| Error::invalid_raw_misbehaviour("invalid client_id".into()))?;

        let header1 = raw
            .header_1
            .ok_or_else(|| Error::invalid_raw_misbehaviour("missing header_1".into()))?
            .try_into()?;

        let header2 = raw
            .header_2
            .ok_or_else(|| Error::invalid_raw_misbehaviour("missing header_2".into()))?
            .try_into()?;

        Ok(Self {
            client_id,
            header1,
            header2,
        })
    }
}

impl From<Misbehaviour> for RawMisbehaviour {
    fn from(value: Misbehaviour) -> Self {
        Self {
            client_id: value.client_id.to_string(),
            header_1: Some(value.header1.into()),
            header_2: Some(value.header2.into()),
        }
    }
}

impl Protobuf<Any> for Misbehaviour {}

impl TryFrom<Any> for Misbehaviour {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            STELLAR_MISBEHAVIOUR_TYPE_URL => RawMisbehaviour::decode(raw.value.as_ref())
                .map_err(|e| Error::decode(e.into()))?
                .try_into()
                .map_err(Into::into),
            _ => Err(Ics02Error::unknown_misbehaviour_type(raw.type_url)),
        }
    }
}

impl From<Misbehaviour> for Any {
    fn from(value: Misbehaviour) -> Self {
        Any {
            type_url: STELLAR_MISBEHAVIOUR_TYPE_URL.to_string(),
            value: Protobuf::<RawMisbehaviour>::encode_vec(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use ibc_proto::google::protobuf::Any;

    use super::Misbehaviour;
    use crate::clients::ics10_stellar::header::Header;
    use crate::clients::ics10_stellar::raw::STELLAR_MISBEHAVIOUR_TYPE_URL;
    use crate::core::ics02_client::misbehaviour::Misbehaviour as Ics2Misbehaviour;
    use crate::core::ics24_host::identifier::ClientId;
    use crate::timestamp::Timestamp;
    use crate::Height;

    fn sample_header(ledger_seq: u32, hash_byte: u8) -> Header {
        Header {
            height: Height::new(0, ledger_seq as u64).unwrap(),
            ledger_hash: [hash_byte; 32],
            timestamp: Timestamp::from_nanoseconds(1_700_000_000_000_000_000).unwrap(),
            ledger_seq,
            scp_envelopes: vec![0x01],
        }
    }

    fn sample_misbehaviour() -> Misbehaviour {
        Misbehaviour::new(
            "07-stellar-0".parse().unwrap(),
            sample_header(500, 0xaa),
            sample_header(500, 0xbb), // same height, different ledger hash
        )
    }

    #[test]
    fn client_id_and_height() {
        let m = sample_misbehaviour();
        assert_eq!(m.client_id(), &"07-stellar-0".parse::<ClientId>().unwrap());
        assert_eq!(m.height(), Height::new(0, 500).unwrap());
    }

    #[test]
    fn roundtrip_raw() {
        use crate::clients::ics10_stellar::raw::RawMisbehaviour;

        let original = sample_misbehaviour();
        let raw = RawMisbehaviour::from(original.clone());
        let recovered = Misbehaviour::try_from(raw).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any() {
        let original = sample_misbehaviour();
        let any = Any::from(original.clone());
        assert_eq!(any.type_url, STELLAR_MISBEHAVIOUR_TYPE_URL);
        let recovered = Misbehaviour::try_from(any).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn missing_header1_returns_error() {
        use crate::clients::ics10_stellar::raw::RawMisbehaviour;

        let raw = RawMisbehaviour {
            client_id: "07-stellar-0".to_string(),
            header_1: None,
            header_2: Some(sample_header(500, 0xbb).into()),
        };
        assert!(Misbehaviour::try_from(raw).is_err());
    }

    #[test]
    fn missing_header2_returns_error() {
        use crate::clients::ics10_stellar::raw::RawMisbehaviour;

        let raw = RawMisbehaviour {
            client_id: "07-stellar-0".to_string(),
            header_1: Some(sample_header(500, 0xaa).into()),
            header_2: None,
        };
        assert!(Misbehaviour::try_from(raw).is_err());
    }

    #[test]
    fn unknown_type_url_returns_error() {
        let any = Any {
            type_url: "/some.other.Misbehaviour".to_string(),
            value: vec![],
        };
        assert!(Misbehaviour::try_from(any).is_err());
    }

    #[test]
    fn display_contains_client_id() {
        let m = sample_misbehaviour();
        let s = format!("{m}");
        assert!(s.contains("07-stellar-0"));
    }
}
