---- MODULE main ----

EXTENDS transfer

\* Trace with a LocalTransfer action
LocalTransferTest == action.name = LocalTransferAction

\* Trace with a CreateChannel action
CreateChannelTest == action.name = CreateChannelAction
\* Trace with an ExpireChannel action
ExpireChannelTest == action.name = ExpireChannelAction

\* Trace with an IBCTransferSendPacket action
IBCTransferSendPacketTest == action.name = IBCTransferSendPacketAction
\* Trace with an IBCTransferReceivePacket action
IBCTransferReceivePacketTest == action.name = IBCTransferReceivePacketAction
\* Trace with an IBCTransferAcknowledgePacket action
IBCTransferAcknowledgePacketTest == action.name = IBCTransferAcknowledgePacketAction
\* Trace with an IBCTransferTimeoutPacket action
IBCTransferTimeoutPacketTest == action.name = IBCTransferTimeoutPacketAction

\* Negate the trace predicate to find counter-example
LocalTransferInv == ~LocalTransferTest
CreateChannelInv == ~CreateChannelTest
ExpireChannelInv == ~ExpireChannelTest
IBCTransferSendPacketInv == ~IBCTransferSendPacketTest
IBCTransferReceivePacketInv == ~IBCTransferReceivePacketTest
IBCTransferAcknowledgePacketInv == ~IBCTransferAcknowledgePacketTest
IBCTransferTimeoutPacketInv == ~IBCTransferTimeoutPacketTest
====
