---- MODULE MC_Transfer ----
EXTENDS Transfer_typedefs

CHAIN_IDS == {1, 2}
N_INITIAL_ACCOUNTS == 2
GENESIS_AMOUNT == 3

VARIABLES
    \* Interchain state
    \* @type: CHAIN_ID -> CHAIN;
    chains,
    \* @type: Bool;
    relayerRunning,
    \* Action performed at current step
    \* @type: [ name: Str ];
    action,
    \* Outcome after action performed at current step
    \* @type: [ name: Str ];
    outcome

INSTANCE Transfer

\* Trace with a LocalTransfer action
LocalTransferTest == action.name = LocalTransferAction

\* Trace with a RestoreRelay action
RestoreRelayTest == action.name = RestoreRelayAction
\* Trace with an InterruptRelay action
InterruptRelayTest == action.name = InterruptRelayAction

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
RestoreRelayInv == ~RestoreRelayTest
InterruptRelayInv == ~InterruptRelayTest
IBCTransferSendPacketInv == ~IBCTransferSendPacketTest
IBCTransferReceivePacketInv == ~IBCTransferReceivePacketTest
IBCTransferAcknowledgePacketInv == ~IBCTransferAcknowledgePacketTest
IBCTransferTimeoutPacketInv == ~IBCTransferTimeoutPacketTest

====
