use flex_error::*;

pub type Error = anyhow::Error;


define_error! { KindError;
    InvalidRawMerkleProof
    | _ | { format_args!("invalid raw merkle proof")},
}