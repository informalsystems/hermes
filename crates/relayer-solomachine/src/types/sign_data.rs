#[derive(Clone)]
pub struct SolomachineSignData {
    pub sequence: u64,
    pub timestamp: u64,
    pub diversifier: String,
    pub path: Vec<u8>,
    pub data: Vec<u8>,
}
