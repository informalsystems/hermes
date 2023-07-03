use crate::core::traits::sync::Async;

pub trait HasCommitmentPrefixType<Counterparty>: Async {
    type CommitmentPrefix: Async;
}

pub trait HasCommitmentProofsType<Counterparty>: Async {
    type CommitmentProofs: Async;
}
