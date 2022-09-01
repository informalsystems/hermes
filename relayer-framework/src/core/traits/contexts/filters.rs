use crate::core::traits::core::Async;

pub trait HasFilters {
    type Filters: Async;

    fn filters(&self) -> &Self::Filters;
}