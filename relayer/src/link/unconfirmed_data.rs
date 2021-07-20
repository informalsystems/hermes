use crate::link::operational_data::OperationalData;

#[derive(Clone)]
pub struct UnconfirmedData {
    pub original_od: OperationalData,
}
