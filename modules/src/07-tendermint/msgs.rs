const TypeMsgCreateClient: &str  = "create_client";
const TypeMsgUpdateClient: &str = "update_client";

use std::time::Duration;

struct MsgCreateClient {
    client_id: String,
    chain_id: String,
    consensus_state: ConsensusState,
    //trusting_period: TrustinPeriod,
    unbonding_period: Duration,
    //signer: Signer,
}

impl Msg for MsgCreateClient {
    fn Type(&self) -> &'static str {
        TypeMsgCreateClient
    }
    fn ValidateBasic(&self) -> error {

    }
    fn GetSignBytes(&self) -> &'static [byte] {

    }
    fn GetSigners(&self) -> &'static [AccAddress] {

    }
}