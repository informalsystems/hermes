---- MODULE main ----

EXTENDS transfer

LocalTransferTest == action.name = LocalTransferAction

CreateChannelTest == action.name = CreateChannelAction
ExpireChannelTest == action.name = ExpireChannelAction

IBCTransferSendPacketTest == action.name = IBCTransferSendPacketAction
IBCTransferReceivePacketTest == action.name = IBCTransferReceivePacketAction
IBCTransferAcknowledgePacketTest == action.name = IBCTransferAcknowledgePacketAction
IBCTransferTimeoutPacketTest == action.name = IBCTransferTimeoutPacketAction

====
