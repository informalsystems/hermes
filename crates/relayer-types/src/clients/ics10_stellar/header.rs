use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::clients::ics10_stellar::error::Error;
use crate::clients::ics10_stellar::raw::{RawHeader, STELLAR_HEADER_TYPE_URL};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::timestamp::Timestamp;
use crate::Height;

/// Stellar light client header.
///
/// Carries an SCP consensus proof (`scp_envelopes`) for a specific ledger.
/// The counterpart chain's `10-stellar` light client verifies the quorum of
/// EXTERNALIZE envelopes to confirm the ledger hash and advance its trusted
/// height.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Header {
    /// IBC consensus height (revision_number = 0, revision_height = ledger_seq)
    pub height: Height,
    /// SHA-256 hash of the LedgerHeader XDR (32 bytes)
    pub ledger_hash: [u8; 32],
    /// Ledger close timestamp
    pub timestamp: Timestamp,
    /// Stellar ledger sequence number
    pub ledger_seq: u32,
    /// XDR-encoded SCP EXTERNALIZE envelopes proving consensus for this ledger
    pub scp_envelopes: Vec<u8>,
}

impl core::fmt::Display for Header {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "StellarHeader {{ height: {}, ledger_seq: {} }}",
            self.height, self.ledger_seq,
        )
    }
}

impl crate::core::ics02_client::header::Header for Header {
    fn client_type(&self) -> ClientType {
        ClientType::Stellar
    }

    fn height(&self) -> Height {
        self.height
    }

    fn timestamp(&self) -> Timestamp {
        self.timestamp
    }
}

// ---------------------------------------------------------------------------
// Protobuf conversions
// ---------------------------------------------------------------------------

impl Protobuf<RawHeader> for Header {}

impl TryFrom<RawHeader> for Header {
    type Error = Error;

    fn try_from(raw: RawHeader) -> Result<Self, Self::Error> {
        let height: Height = raw
            .height
            .ok_or_else(|| Error::invalid_header("missing height".into()))?
            .try_into()
            .map_err(|_| Error::invalid_header("invalid height".into()))?;

        let ledger_hash: [u8; 32] = raw
            .ledger_hash
            .try_into()
            .map_err(|_| Error::invalid_header("ledger_hash must be exactly 32 bytes".into()))?;

        let timestamp = Timestamp::from_nanoseconds(raw.timestamp_ns)
            .map_err(|e| Error::invalid_header(e.to_string()))?;

        Ok(Self {
            height,
            ledger_hash,
            timestamp,
            ledger_seq: raw.ledger_seq,
            scp_envelopes: raw.scp_envelopes,
        })
    }
}

impl From<Header> for RawHeader {
    fn from(value: Header) -> Self {
        Self {
            height: Some(value.height.into()),
            ledger_hash: value.ledger_hash.to_vec(),
            timestamp_ns: value.timestamp.nanoseconds(),
            ledger_seq: value.ledger_seq,
            scp_envelopes: value.scp_envelopes,
        }
    }
}

impl Protobuf<Any> for Header {}

impl TryFrom<Any> for Header {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            STELLAR_HEADER_TYPE_URL => RawHeader::decode(raw.value.as_ref())
                .map_err(|e| Error::decode(e.into()))?
                .try_into()
                .map_err(Into::into),
            _ => Err(Ics02Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<Header> for Any {
    fn from(value: Header) -> Self {
        Any {
            type_url: STELLAR_HEADER_TYPE_URL.to_string(),
            value: Protobuf::<RawHeader>::encode_vec(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use ibc_proto::google::protobuf::Any;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use super::Header;
    use crate::clients::ics10_stellar::raw::{RawHeader, STELLAR_HEADER_TYPE_URL};
    use crate::core::ics02_client::header::Header as IbcHeader;
    use crate::core::ics02_client::header::AnyHeader;
    use crate::core::ics02_client::client_type::ClientType;
    use crate::timestamp::Timestamp;
    use crate::Height;

    fn sample_header() -> Header {
        Header {
            height: Height::new(0, 1234).unwrap(),
            ledger_hash: [0xab; 32],
            timestamp: Timestamp::from_nanoseconds(1_700_000_000_000_000_000).unwrap(),
            ledger_seq: 1234,
            scp_envelopes: vec![0x01, 0x02, 0x03],
        }
    }

    #[test]
    fn client_type_is_stellar() {
        assert_eq!(sample_header().client_type(), ClientType::Stellar);
    }

    #[test]
    fn height_and_timestamp_accessors() {
        let h = sample_header();
        assert_eq!(h.height(), Height::new(0, 1234).unwrap());
        assert_eq!(
            h.timestamp(),
            Timestamp::from_nanoseconds(1_700_000_000_000_000_000).unwrap()
        );
    }

    #[test]
    fn roundtrip_raw() {
        let original = sample_header();
        let raw = RawHeader::from(original.clone());
        let recovered = Header::try_from(raw).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any() {
        let original = sample_header();
        let any = Any::from(original.clone());
        assert_eq!(any.type_url, STELLAR_HEADER_TYPE_URL);
        let recovered = Header::try_from(any).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any_header_enum() {
        let original = sample_header();
        let any_header = AnyHeader::Stellar(original.clone());
        let any = Any::from(any_header);
        let recovered = AnyHeader::try_from(any).unwrap();
        assert_eq!(recovered, AnyHeader::Stellar(original));
    }

    #[test]
    fn missing_height_returns_error() {
        let raw = RawHeader {
            height: None,
            ledger_hash: vec![0u8; 32],
            timestamp_ns: 1_000_000,
            ledger_seq: 1,
            scp_envelopes: vec![],
        };
        assert!(Header::try_from(raw).is_err());
    }

    #[test]
    fn wrong_ledger_hash_length_returns_error() {
        let raw = RawHeader {
            height: Some(RawHeight {
                revision_number: 0,
                revision_height: 1,
            }),
            ledger_hash: vec![0u8; 16], // wrong: must be 32 bytes
            timestamp_ns: 1_000_000,
            ledger_seq: 1,
            scp_envelopes: vec![],
        };
        assert!(Header::try_from(raw).is_err());
    }

    #[test]
    fn unknown_type_url_returns_error() {
        let any = Any {
            type_url: "/some.other.Header".to_string(),
            value: vec![],
        };
        assert!(Header::try_from(any).is_err());
    }

    #[test]
    fn display_format() {
        let h = sample_header();
        let s = format!("{h}");
        assert!(s.contains("1234")); // ledger_seq / revision_height both 1234
    }
}
