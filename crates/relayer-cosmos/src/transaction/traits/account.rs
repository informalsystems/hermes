use ibc_relayer::chain::cosmos::types::account::{Account, AccountSequence};

pub trait HasAccount {
    fn account(&self) -> &Account;
}

pub trait CanUpdateAccountSequence {
    fn update_account_sequence(&self, sequence: AccountSequence);
}

pub trait MaybeHasAccount {
    fn maybe_account(&self) -> Option<&Account>;

    fn update_account(&self, account: &Account);
}
