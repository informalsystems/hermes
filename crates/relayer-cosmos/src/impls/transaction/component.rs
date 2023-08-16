use ibc_relayer_components::core::traits::component::DelegateComponent;
use ibc_relayer_components_extra::components::extra::transaction::ExtraTxComponents;

use crate::contexts::transaction::CosmosTxContext;

pub struct CosmosTxComponents;

impl<Name> DelegateComponent<Name> for CosmosTxContext {
    type Delegate = ExtraTxComponents<CosmosTxComponents>;
}
