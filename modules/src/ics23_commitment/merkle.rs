use crate::ics23_commitment::commitment::CommitmentPrefix;

use ibc_proto::ibc::core::commitment::v1::MerklePath;

pub fn apply_prefix(
    prefix: &CommitmentPrefix,
    _path: String,
) -> Result<MerklePath, Box<dyn std::error::Error>> {
    if prefix.is_empty() {
        return Err("empty prefix".into());
    }

    // TODO
    Ok(MerklePath { key_path: None })
}
