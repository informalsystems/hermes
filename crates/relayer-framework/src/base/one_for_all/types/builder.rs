use crate::base::one_for_all::traits::builder::OfaBuilder;

pub struct OfaBuilderWrapper<Builder>
where
    Builder: OfaBuilder,
{
    pub builder: Builder,
}
