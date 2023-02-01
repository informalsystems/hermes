use core::marker::PhantomData;
use ibc_framework::core::impls::handlers::update_client::lift::LiftClientUpdateHandler;
use ibc_framework::core::traits::handlers::update_client::{
    AnyUpdateClientHandler, UpdateClientHandler,
};

use crate::all_for_one::traits::dynamic::AfoDynamicChainContext;
use crate::all_for_one::traits::tendermint::AfoTendermintOnlyChainContext;
use crate::clients::tendermint::client::TendermintClient;

pub fn can_build_tendermint_update_handler<Context>(
) -> PhantomData<impl UpdateClientHandler<Context>>
where
    Context: AfoTendermintOnlyChainContext,
{
    PhantomData::<TendermintClient>
}

pub fn can_build_tendermint_any_update_handler<Context>(
) -> PhantomData<impl AnyUpdateClientHandler<Context>>
where
    Context: AfoTendermintOnlyChainContext,
{
    PhantomData::<LiftClientUpdateHandler<TendermintClient>>
}

pub fn can_build_dynamic_tendermint_any_update_handler<Context>(
) -> PhantomData<impl AnyUpdateClientHandler<Context>>
where
    Context: AfoDynamicChainContext,
{
    PhantomData::<LiftClientUpdateHandler<TendermintClient>>
}
