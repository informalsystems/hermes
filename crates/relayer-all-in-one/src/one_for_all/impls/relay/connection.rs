use async_trait::async_trait;

use ibc_relayer_components::relay::impls::connection::open_init::{
    InitializeConnection, InjectMissingConnectionInitEventError,
};
use ibc_relayer_components::relay::traits::connection::open_init::{
    CanInitConnection, ConnectionInitializer,
};

use crate::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

impl<Relay> InjectMissingConnectionInitEventError for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_connection_init_event_error(&self) -> Relay::Error {
        self.relay.missing_connection_init_event_error()
    }
}

#[async_trait]
impl<Relay> CanInitConnection for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn init_connection(
        &self,
        init_connection_options: &<Relay::SrcChain as OfaIbcChain<Relay::DstChain>>::InitConnectionOptions,
    ) -> Result<<Relay::SrcChain as OfaChain>::ConnectionId, Self::Error> {
        InitializeConnection::init_connection(self, init_connection_options).await
    }
}
