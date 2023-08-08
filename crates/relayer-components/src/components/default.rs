use core::marker::PhantomData;

use crate::relay::impls::client::update::BuildUpdateClientMessages;
use crate::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::std_prelude::*;

pub struct DefaultComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::derive_update_client_message_builder!(
    DefaultComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

crate::derive_chain_status_querier!(DefaultComponents<BaseComponents>, BaseComponents,);
