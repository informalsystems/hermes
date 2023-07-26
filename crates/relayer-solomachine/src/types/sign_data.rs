#[derive(Clone)]
pub struct SolomachineSignData {
    pub diversifier: String,
    pub sequence: u64,
    pub timestamp: u64,
    pub path: Vec<u8>,
    pub data: Vec<u8>,
}

pub fn membership_sign_data(
    diversifier: &str,
    sequence: u64,
    timestamp: u64,
    path: &str,
    data: &[u8],
) -> SolomachineSignData {
    SolomachineSignData {
        diversifier: diversifier.to_string(),
        sequence,
        timestamp,
        path: path.into(),
        data: data.into(),
    }
}

pub fn non_membership_sign_data(
    diversifier: &str,
    sequence: u64,
    timestamp: u64,
    path: &str,
) -> SolomachineSignData {
    SolomachineSignData {
        diversifier: diversifier.to_string(),
        sequence,
        timestamp,
        path: path.into(),
        data: Vec::new(),
    }
}
