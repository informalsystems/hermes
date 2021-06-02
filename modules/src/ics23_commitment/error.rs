use flex_error::*;

pub type Error = anyhow::Error;

define_error! {
    #[derive(Debug)]
    CommitmentError {
        InvalidRawMerkleProof
        [DisplayError<Error>]
        | _ | { format_args!("invalid raw merkle proof")},
    }
}
