use ibc_relayer_framework::full::all_for_one::relay::AfoFullRelayContext;

use crate::cosmos::base::all_for_one::relay::AfoCosmosRelayContext;

pub trait AfoCosmosFullRelayContext: AfoCosmosRelayContext + AfoFullRelayContext {}

impl<Relay> AfoCosmosFullRelayContext for Relay where
    Relay: AfoCosmosRelayContext + AfoFullRelayContext
{
}
