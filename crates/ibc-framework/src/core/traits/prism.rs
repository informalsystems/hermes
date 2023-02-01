use crate::core::traits::sync::Async;

pub trait Prism<Data, SubData>: Async {
    fn into(subdata: SubData) -> Data;

    fn try_from(data: Data) -> Option<SubData>;

    fn try_from_ref(data: &Data) -> Option<&SubData>;
}
