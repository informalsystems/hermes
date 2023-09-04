use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components_extra::components::extra::transaction::ExtraTxComponents;

use crate::contexts::transaction::CosmosTxContext;

pub struct CosmosTxComponents;

impl HasComponents for CosmosTxContext {
    type Components = ExtraTxComponents<CosmosTxComponents>;
}
