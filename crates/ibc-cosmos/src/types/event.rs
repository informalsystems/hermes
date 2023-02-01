use ibc::core::ics24_host::identifier::ClientId;
use ibc::Height;
use ibc_framework::core::traits::client::HasAnyClientTypes;

pub enum IbcEvent<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    UpdateClient(UpdateClientEvent<AnyClient>),
    Misbehavior(MisbehaviorEvent<AnyClient>),
}

pub struct UpdateClientEvent<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    pub client_id: ClientId,
    pub client_type: AnyClient::ClientType,
    pub consensus_height: Height,
    pub header: AnyClient::AnyClientHeader,
}

pub struct MisbehaviorEvent<AnyClient>
where
    AnyClient: HasAnyClientTypes,
{
    pub client_id: ClientId,
    pub client_type: AnyClient::ClientType,
    pub consensus_height: Height,
    pub header: AnyClient::AnyClientHeader,
}
