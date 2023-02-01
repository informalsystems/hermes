use crate::core::traits::client::{HasAnyClientTypes, HasClientTypes};

pub type ClientType<Context> = <Context as HasAnyClientTypes>::ClientType;

pub type AnyClientState<Context> = <Context as HasAnyClientTypes>::AnyClientState;

pub type ClientState<Context> = <Context as HasClientTypes>::ClientState;

pub type AnyConsensusState<Context> = <Context as HasAnyClientTypes>::AnyConsensusState;

pub type ConsensusState<Context> = <Context as HasClientTypes>::ConsensusState;

pub type AnyClientHeader<Context> = <Context as HasAnyClientTypes>::AnyClientHeader;

pub type ClientHeader<Context> = <Context as HasClientTypes>::ClientHeader;
