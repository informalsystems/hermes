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
    #[prost(string, tag = "1")]
    pub name: ::prost::alloc::string::String,
    /// Deprecated: Time based upgrades have been deprecated. Time based upgrade logic
    /// has been removed from the SDK.
    /// If this field is not empty, an error will be thrown.
    #[deprecated]
    #[prost(message, optional, tag = "2")]
    pub time: ::core::option::Option<::prost_types::Timestamp>,
    /// The height at which the upgrade must be performed.
    /// Only used if Time is not set.
    #[prost(int64, tag = "3")]
    pub height: i64,
    /// Any application specific upgrade info to be included on-chain
    /// such as a git commit that validators could automatically upgrade to
    #[prost(string, tag = "4")]
    pub info: ::prost::alloc::string::String,
    /// Deprecated: UpgradedClientState field has been deprecated. IBC upgrade logic has been
    /// moved to the IBC module in the sub module 02-client.
    /// If this field is not empty, an error will be thrown.
    #[deprecated]
    #[prost(message, optional, tag = "5")]
    pub upgraded_client_state: ::core::option::Option<::prost_types::Any>,
}
/// SoftwareUpgradeProposal is a gov Content type for initiating a software
/// upgrade.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SoftwareUpgradeProposal {
    #[prost(string, tag = "1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub description: ::prost::alloc::string::String,
    #[prost(message, optional, tag = "3")]
    pub plan: ::core::option::Option<Plan>,
}
/// CancelSoftwareUpgradeProposal is a gov Content type for cancelling a software
/// upgrade.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CancelSoftwareUpgradeProposal {
    #[prost(string, tag = "1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub description: ::prost::alloc::string::String,
}
/// ModuleVersion specifies a module and its consensus version.
///
/// Since: cosmos-sdk 0.43
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ModuleVersion {
    /// name of the app module
    #[prost(string, tag = "1")]
    pub name: ::prost::alloc::string::String,
    /// consensus version of the app module
    #[prost(uint64, tag = "2")]
    pub version: u64,
}
/// QueryCurrentPlanRequest is the request type for the Query/CurrentPlan RPC
/// method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCurrentPlanRequest {}
/// QueryCurrentPlanResponse is the response type for the Query/CurrentPlan RPC
/// method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCurrentPlanResponse {
    /// plan is the current upgrade plan.
    #[prost(message, optional, tag = "1")]
    pub plan: ::core::option::Option<Plan>,
}
/// QueryCurrentPlanRequest is the request type for the Query/AppliedPlan RPC
/// method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppliedPlanRequest {
    /// name is the name of the applied plan to query for.
    #[prost(string, tag = "1")]
    pub name: ::prost::alloc::string::String,
}
/// QueryAppliedPlanResponse is the response type for the Query/AppliedPlan RPC
/// method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppliedPlanResponse {
    /// height is the block height at which the plan was applied.
    #[prost(int64, tag = "1")]
    pub height: i64,
}
/// QueryUpgradedConsensusStateRequest is the request type for the Query/UpgradedConsensusState
/// RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUpgradedConsensusStateRequest {
    /// last height of the current chain must be sent in request
    /// as this is the height under which next consensus state is stored
    #[prost(int64, tag = "1")]
    pub last_height: i64,
}
/// QueryUpgradedConsensusStateResponse is the response type for the Query/UpgradedConsensusState
/// RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUpgradedConsensusStateResponse {
    /// Since: cosmos-sdk 0.43
    #[prost(bytes = "vec", tag = "2")]
    pub upgraded_consensus_state: ::prost::alloc::vec::Vec<u8>,
}
/// QueryModuleVersionsRequest is the request type for the Query/ModuleVersions
/// RPC method.
///
/// Since: cosmos-sdk 0.43
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryModuleVersionsRequest {
    /// module_name is a field to query a specific module
    /// consensus version from state. Leaving this empty will
    /// fetch the full list of module versions from state
    #[prost(string, tag = "1")]
    pub module_name: ::prost::alloc::string::String,
}
/// QueryModuleVersionsResponse is the response type for the Query/ModuleVersions
/// RPC method.
///
/// Since: cosmos-sdk 0.43
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryModuleVersionsResponse {
    /// module_versions is a list of module names with their consensus versions.
    #[prost(message, repeated, tag = "1")]
    pub module_versions: ::prost::alloc::vec::Vec<ModuleVersion>,
}
