--------------------- MODULE ICS18Environment_apalache ---------------------

EXTENDS ICS18Environment

OVERRIDE_MaxHeight == 2
OVERRIDE_MaxPacketSeq == 2
OVERRIDE_ClientDatagramsRelayer1 == TRUE 
OVERRIDE_ConnectionDatagramsRelayer1 == TRUE
OVERRIDE_ChannelDatagramsRelayer1 == TRUE
OVERRIDE_ClientDatagramsRelayer2 == TRUE
OVERRIDE_ConnectionDatagramsRelayer2 == TRUE
OVERRIDE_ChannelDatagramsRelayer2 == TRUE
OVERRIDE_ChannelOrdering == "UNORDERED"

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 14:30:07 CEST 2020 by ilinastoilkovska
\* Created Wed Aug 05 11:27:26 CEST 2020 by ilinastoilkovska
