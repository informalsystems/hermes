use std::convert::TryFrom;

use prost_types::Any;
use tendermint_proto::Protobuf;

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{Error, Kind};
use crate::ics07_tendermint::header::Header as TmHeader;
#[cfg(any(test, feature = "mocks"))]
use crate::mock::header::MockHeader;
use crate::Height;

pub const TENDERMINT_HEADER_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.Header";

#[cfg(any(test, feature = "mocks"))]
pub const MOCK_HEADER_TYPE_URL: &str = "/ibc.mock.Header";

/// Abstract of consensus state update information
#[dyn_clonable::clonable]
pub trait Header: Clone + std::fmt::Debug + Send + Sync {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;

    /// Wrap into an `AnyHeader`
    fn wrap_any(self) -> AnyHeader;
}

#[derive(Clone, Debug, PartialEq)] // TODO: Add Eq bound once possible
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TmHeader),

    #[cfg(any(test, feature = "mocks"))]
    Mock(MockHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(header) => header.height(),
        }
    }

    fn wrap_any(self) -> AnyHeader {
        self
    }
}

impl Protobuf<Any> for AnyHeader {}

impl TryFrom<Any> for AnyHeader {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            TENDERMINT_HEADER_TYPE_URL => Ok(AnyHeader::Tendermint(
                TmHeader::decode_vec(&raw.value).map_err(|e| Kind::InvalidRawHeader.context(e))?,
            )),

            #[cfg(any(test, feature = "mocks"))]
            MOCK_HEADER_TYPE_URL => Ok(AnyHeader::Mock(
                MockHeader::decode_vec(&raw.value)
                    .map_err(|e| Kind::InvalidRawHeader.context(e))?,
            )),

            _ => Err(Kind::UnknownHeaderType(raw.type_url).into()),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: header.encode_vec().unwrap(),
            },
            #[cfg(any(test, feature = "mocks"))]
            AnyHeader::Mock(header) => Any {
                type_url: MOCK_HEADER_TYPE_URL.to_string(),
                value: header.encode_vec().unwrap(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use prost_types::Any;
    use crate::ics02_client::client_header::AnyHeader;
    use tendermint_proto::Protobuf;

    #[test]
    fn header_event_deserialization() {
        let header: String = "\n&/ibc.lightclients.tendermint.v1.Header\u{12}�\u{6}\n�\u{4}\n�\u{3}\n\u{2}\u{8}\u{b}\u{12}\u{5}ibc-1\u{18}�\u{18}\"\u{c}\u{8}ȋ��\u{6}\u{10}����\u{2}*H\n xVW���\u{1a}嵌���>e\u{1f}j����|\t��0%��}��\u{12}$\u{8}\u{1}\u{12} �\u{1d}>x��5�j����5��G(���s�\u{13}/<n\u{1a}�I��2 ���ꑤ��CОlj\u{1}�|D�w�)\u{7a9}\u{6}M��a\u{18}�F`: ���B��\u{1c}\u{14}���șo�$\'�A�d��L���\u{1b}xR�UB A��a�V��{�n#\u{1c}�\u{2}b�6QݥD���k��ʤg�J A��a�V��{�n#\u{1c}�\u{2}b�6QݥD���k��ʤg�R \u{4}���}�(?w����<D�X�ߊ���t\u{5}ط�ڭ�/Z \u{18}h\u{1a}�\u{11}����\u{b}z\u{2}�N�s�}r\u{1}n\u{c}�\u{8}�E�d,���b ���B��\u{1c}\u{14}���șo�$\'�A�d��L���\u{1b}xR�Uj ���B��\u{1c}\u{14}���șo�$\'�A�d��L���\u{1b}xR�Ur\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{12}�\u{1}\u{8}�\u{18}\u{1a}H\n J�I�;w��(;�\nnj��r\u{1}����/�S �|(\u{14}�;\u{12}$\u{8}\u{1}\u{12} �g�᮶��\'�����\u{742}]�#�;��K�\r9�T��x\"h\u{8}\u{2}\u{12}\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{1a}\u{c}\u{8}ɋ��\u{6}\u{10}����\u{3}\"@���+ƨ\u{4}s\u{1}��\u{1a};\u{12}��\u{0}f\u{1e}�\u{1b}(\u{10}�kB/B\u{12}��0\u{1f}\u{19}���)�����b}�j�9��I�z]\u{12}��L71;7\n\u{12}�\u{1}\n>\n\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{12}\"\n �ŧ(�fl&&FR�s��o�;�b4UҘ�)�J�\u{1e}��\u{18}��\u{6}\u{12}>\n\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{12}\"\n �ŧ(�fl&&FR�s��o�;�b4UҘ�)�J�\u{1e}��\u{18}��\u{6}\u{18}��\u{6}\u{1a}\u{5}\u{8}\u{1}\u{10}�\u{16}\"�\u{1}\n>\n\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{12}\"\n �ŧ(�fl&&FR�s��o�;�b4UҘ�)�J�\u{1e}��\u{18}��\u{6}\u{12}>\n\u{14}(��\u{f}�;|A\u{c}������Qk�\u{5}�\u{12}\"\n �ŧ(�fl&&FR�s��o�;�b4UҘ�)�J�\u{1e}��\u{18}��\u{6}\u{18}��\u{6}".to_string();
        let valid_raw_bytes = header.as_bytes();

        let _any_prost: Any = prost::Message::decode(valid_raw_bytes).unwrap();
        let _any_header: AnyHeader = Protobuf::decode(valid_raw_bytes).unwrap();
    }
}