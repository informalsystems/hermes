use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components_extra::components::extra::transaction::ExtraTxComponents;

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext, Name> DelegateComponent<Name> for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Delegate = ExtraTxComponents<OfaComponents>;
}
