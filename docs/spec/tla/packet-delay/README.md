# TLA+ Specification of IBC Packet Transmission with Packet Delay (deprecated)

This document describes the TLA+ specification of an IBC packet transmission with 
packet delays. 
IBC packet transmission with packet delays ensures that 
packet-related data should be accepted only after some delay has passed since the corresponding header is installed. 
This allows a correct relayer to intervene if the header is from a fork and shutdown the IBC handler, preventing damage at the application level.

This TLA+ specification was used during the [design process](https://github.com/cosmos/cosmos-sdk/pull/7884) of the IBC connection-specified delay, where packet delay was a time duration. 
Later, this design was augmented by adding a second delay parameter, in 
terms of number of blocks; called [hybrid packet delay](https://github.com/cosmos/ibc/issues/539).

## The Model of the Protocol

