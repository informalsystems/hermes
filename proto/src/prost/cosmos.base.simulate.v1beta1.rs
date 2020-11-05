/// SimulateRequest is the request type for the SimulateServiceService.Simulate
/// RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SimulateRequest {
    /// tx is the transaction to simulate.
    #[prost(message, optional, tag="1")]
    pub tx: ::std::option::Option<super::super::super::tx::v1beta1::Tx>,
}
/// SimulateResponse is the response type for the
/// SimulateServiceService.SimulateRPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SimulateResponse {
    /// gas_info is the information about gas used in the simulation.
    #[prost(message, optional, tag="1")]
    pub gas_info: ::std::option::Option<super::super::abci::v1beta1::GasInfo>,
    /// result is the result of the simulation.
    #[prost(message, optional, tag="2")]
    pub result: ::std::option::Option<super::super::abci::v1beta1::Result>,
}
