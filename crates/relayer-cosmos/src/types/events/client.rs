use ibc_relayer_types::core::ics24_host::identifier::ClientId;

pub struct CosmosCreateClientEvent {
    pub client_id: ClientId,
}
