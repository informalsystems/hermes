---- MODULE main ----

EXTENDS transfer

CreateChannel == action.name = CreateChannelAction
PacketAcknowledgedTest == action.name = IBCTransferAcknowledgePacketAction
PacketTimeoutTest == action.name = IBCTransferAcknowledgePacketAction

Invariant ==
    ~CreateChannel

====