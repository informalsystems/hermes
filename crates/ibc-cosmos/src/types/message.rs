use ibc::core::ics24_host::identifier::ClientId;
use ibc::signer::Signer;
use ibc_framework::core::traits::client::HasAnyClientTypes;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IbcMessageType {
    UpdateClient,
}

pub enum IbcMessage<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    UpdateClient(UpdateClientMessage<AnyClient>),
}

impl<AnyClient> IbcMessage<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    pub fn message_type(&self) -> IbcMessageType {
        match self {
            Self::UpdateClient(_) => IbcMessageType::UpdateClient,
        }
    }
}

pub struct UpdateClientMessage<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    pub client_id: ClientId,
    pub client_header: AnyClient::AnyClientHeader,
    pub signer: Signer,
}
