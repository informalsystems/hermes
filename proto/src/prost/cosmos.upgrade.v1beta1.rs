/// Plan specifies information about a planned upgrade and when it should occur.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Plan {
    /// Sets the name for the upgrade. This name will be used by the upgraded
    /// version of the software to apply any special "on-upgrade" commands during
    /// the first BeginBlock method after the upgrade is applied. It is also used
    /// to detect whether a software version can handle a given upgrade. If no
    /// upgrade handler with this name has been set in the software, it will be
    /// assumed that the software is out-of-date when the upgrade Time or Height is
    /// reached and the software will exit.
    #[prost(string, tag="1")]
    pub name: ::prost::alloc::string::String,
    /// The time after which the upgrade must be performed.
    /// Leave set to its zero value to use a pre-defined Height instead.
    #[prost(message, optional, tag="2")]
    pub time: ::core::option::Option<::prost_types::Timestamp>,
    /// The height at which the upgrade must be performed.
    /// Only used if Time is not set.
    #[prost(int64, tag="3")]
    pub height: i64,
    /// Any application specific upgrade info to be included on-chain
    /// such as a git commit that validators could automatically upgrade to
    #[prost(string, tag="4")]
    pub info: ::prost::alloc::string::String,
}
/// SoftwareUpgradeProposal is a gov Content type for initiating a software
/// upgrade.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SoftwareUpgradeProposal {
    #[prost(string, tag="1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub description: ::prost::alloc::string::String,
    #[prost(message, optional, tag="3")]
    pub plan: ::core::option::Option<Plan>,
}
/// CancelSoftwareUpgradeProposal is a gov Content type for cancelling a software
/// upgrade.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CancelSoftwareUpgradeProposal {
    #[prost(string, tag="1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub description: ::prost::alloc::string::String,
}
