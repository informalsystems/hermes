---- MODULE Transfer ----
EXTENDS Apalache, Sequences, Integers, Transfer_typedefs

CONSTANTS
    \* Set of blockchain names
    \* @type: Set(CHAIN_ID);
    CHAIN_IDS,
    \* Number of accounts per blockchain
    \* @type: ACCOUNT_ID;
    N_INITIAL_ACCOUNTS,
    \* Genesis balance per account
    \* @type: Int;
    GENESIS_AMOUNT

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

\* Account IDs starts from 1
\* @type: () => Set(ACCOUNT_ID);
ACCOUNT_IDS == 1..N_INITIAL_ACCOUNTS

\* Actions
NullAction == "Null"
LocalTransferAction == "LocalTransfer"
RestoreRelayAction == "RestoreRelay"
InterruptRelayAction == "InterruptRelay"
IBCTransferSendPacketAction == "IBCTransferSendPacket"
IBCTransferReceivePacketAction == "IBCTransferReceivePacket"
IBCTransferAcknowledgePacketAction == "IBCTransferAcknowledgePacket"
IBCTransferTimeoutPacketAction == "IBCTransferTimeoutPacket"

\* Outcomes
SuccessOutcome == "Success"
ErrorOutcome == "Error"

\* @type: (CHAIN_ID) => CHAIN;
Genesis(chainId) ==
    LET nativeDenom == chainId IN [
    \* Name of the chain
    id |-> chainId,

    \* Bank data for this chain
    \* To support different cross-chain(ibc) denoms, it is a 2D map.
    \* `accountId` has `bank[accountId][denomId]` many `denomId`.
    bank |-> [accountId \in ACCOUNT_IDS |-> [denom \in {nativeDenom} |-> GENESIS_AMOUNT]],
    \* Record of circulating native and cross-chain(ibc) token sourced at this chain
    supply |-> [denom \in {nativeDenom} |-> GENESIS_AMOUNT * N_INITIAL_ACCOUNTS ],

    \* Record of packets originated from this chain
    localPackets |-> [
        \* A table of packets with packetId
        list |-> SetAsFun({}),
        \* Set of packetIds of packets which are not yet acknowledged by destination chain
        pending |-> {},
        \* Set of packetIds of packets which are not delivered to destrination chain within timeout block height
        expired |-> {},
        \* Set of packetIds of packets which are acknowledged by destination chain
        success |-> {}
    ],

    \* Escrow balance per chain
    escrow |-> [cId \in CHAIN_IDS \ {chainId} |-> SetAsFun({})],

    \* Record of packets receiveed from other chains
    \* Packets are maintained using the channelId, it was received at.
    \* Note: A pair of chain may have multiple channels in the past.
    remotePackets |-> SetAsFun({}),

    nextPacketId |-> 0
]

\* Get balance of denom in a bank
\* @type: (BANK, DENOM_ID) => Int;
GetDenomFromBank(bank, denom) ==
    IF denom \in DOMAIN bank THEN bank[denom]
    ELSE 0

\* Add an entry to a map if its key does not exists
\* Else update the existing entry
\* @type: (k -> v, k, v) => (k -> v);
AddOrUpdateEntry(func, key, value) ==
    IF key \in DOMAIN func THEN [func EXCEPT ![key] = value]
    ELSE [x \in {key} \union DOMAIN func |-> IF x = key THEN value ELSE func[x]]


(*
We will model TokenTransfer using following actions.

LocalTransfer                : on-chain transfer

InterruptRelay               : Interrupt relaying
RestoreRelay                 : Restore relaying

IBCTransferSendPacket        : account in source chain tries to send denom to an account in target chain
IBCTransferReceivePacket     : account in target chain receives the denom sent from account in source chain
IBCTransferAcknowledgePacket : the transaction is acknowledged. source chain completes the transaction.
IBCTransferTimeoutPacket     : the transfer is timed-out. balance is refunded to source account.
*)

\* Checks if the source account has enough balance
\* @type: (CHAIN, ACCOUNT_ID, DENOM_ID, Int) => Bool;
HasEnoughBalance(chain, source, denom, amount) ==
    /\ source \in DOMAIN chain.bank
    /\ denom \in DOMAIN chain.bank[source]
    /\ chain.bank[source][denom] >= amount

\* Updated bank after local transfer
\* @type: (CHAIN, ACCOUNT_ID, ACCOUNT_ID, DENOM_ID, Int) => CHAIN;
LocalTransfer(chain, source, target, denom, amount) ==
    [
        chain EXCEPT
        !.bank = [
            @ EXCEPT
            ![source] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) - amount),
            ![target] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ]
    ]

\* Next operator for LocalTransfer
\* @type: () => Bool;
LocalTransferNext ==
    \E chainId \in CHAIN_IDS:
        \E source, target \in ACCOUNT_IDS:
            source /= target /\
            \E amount \in 1..10:
                LET
                chain == chains[chainId]
                denom == chain.id IN
                /\ HasEnoughBalance(chain, source, denom, amount)
                /\ chains' = [
                        chains EXCEPT
                        ![chainId] = LocalTransfer(@, source, target, chain.id, amount)
                    ]
                /\ action' = [
                        name |-> LocalTransferAction,
                        chainId |-> chainId,
                        source |-> source,
                        target |-> target,
                        denom |-> denom,
                        amount |-> amount
                    ]
                /\ outcome' = [ name |-> SuccessOutcome ]
                /\ UNCHANGED relayerRunning

\* Next operator for RestoreRelay
\* @type: () => Bool;
RestoreRelayNext ==
    /\ relayerRunning = FALSE
    /\ relayerRunning' = TRUE
    /\ UNCHANGED chains
    /\ action' = [name |-> RestoreRelayAction]
    /\ outcome' = [name |-> SuccessOutcome]

\* Next operator for InterruptRelay
\* @type: () => Bool;
InterruptRelayNext ==
    /\ relayerRunning = TRUE
    /\ relayerRunning' = FALSE
    /\ UNCHANGED chains
    /\ action' = [name |-> InterruptRelayAction]
    /\ outcome' = [name |-> SuccessOutcome]

\* Checks if there exists a channel between two chains
\* @type: () => Bool;
IBCTransferSendPacketCondition ==
    relayerRunning

\* Creates an IBCPacket with the necessary information and adds it to pending packets
\* @type: (CHAIN, ACCOUNT_ID, CHAIN, ACCOUNT_ID, DENOM_ID, Int) => CHAIN;
IBCTransferSendPacket(sourceChain, source, targetChain, target, denom, amount) ==
    [
        sourceChain EXCEPT
        !.bank = [@ EXCEPT
            ![source] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) - amount)
        ],
        !.escrow = [@ EXCEPT
            ![targetChain.id] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ],
        !.localPackets = [@ EXCEPT
            !.list = AddOrUpdateEntry(@,
                sourceChain.nextPacketId,
                [
                    id |-> sourceChain.nextPacketId,
                    from |-> source,
                    sourceChainId |-> sourceChain.id,
                    to |-> target,
                    targetChainId |-> targetChain.id,
                    denom |-> denom,
                    amount |-> amount
                ]
            ),
            !.pending = @ \union {sourceChain.nextPacketId}
        ],
        !.nextPacketId = @ + 1
    ]

\* Next operator for IBCTransferSendPacket
IBCTransferSendPacketNext ==
    \E chainId1, chainId2 \in CHAIN_IDS:
        chainId1 /= chainId2 /\
        \E acc1, acc2 \in ACCOUNT_IDS:
            \E denom \in DOMAIN chains[chainId1].supply:
                \E amount \in 1..10:
                    /\ IBCTransferSendPacketCondition
                    /\ HasEnoughBalance(chains[chainId1], acc1, denom, amount)
                    /\ chains' = [chains EXCEPT
                            ![chainId1] = IBCTransferSendPacket(chains[chainId1], acc1, chains[chainId2], acc2, denom, amount)
                        ]
                    /\ action' = [
                            name |-> IBCTransferSendPacketAction,
                            packet |-> chains'[chainId1].localPackets.list[chains[chainId1].nextPacketId]
                        ]
                    /\ outcome' = [name |-> SuccessOutcome]
                    /\ UNCHANGED relayerRunning

\* TODO:
\*  append CHANNEL_ID/PORT_ID for source zone
\*  trim CHANNEL_ID/PORT_ID for sink zone
\* @type: (DENOM_ID, CHAIN_ID) => DENOM_ID;
TransformDenom(denom, targetChainId) ==
    denom

\* Process an IBC packet at targetChain
\* @type: (PACKET) => CHAIN;
IBCTransferReceivePacket(packet) ==
    LET
    targetChainId == packet.targetChainId
    sourceChainId == packet.sourceChainId
    destination == packet.to
    denom == TransformDenom(packet.denom, targetChainId)
    amount == packet.amount
    targetChain == chains[targetChainId]
    IN
    [
        targetChain EXCEPT
        !.bank = [@ EXCEPT
            ![destination] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ],
        !.supply = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount),
        !.remotePackets = AddOrUpdateEntry(
            @,
            sourceChainId,
            AddOrUpdateEntry(
                IF sourceChainId \in DOMAIN @ THEN @[sourceChainId] ELSE SetAsFun({}),
                packet.id,
                packet
            )
        )
    ]

\* Checks if the packet is not processed by the targetChain
\* @type: (PACKET, CHAIN) => Bool;
IBCTransferReceivePacketCondition(packet, targetChain) ==
    /\ relayerRunning
    /\ \/ packet.sourceChainId \notin DOMAIN targetChain.remotePackets
       \/ packet.id \notin DOMAIN targetChain.remotePackets[packet.sourceChainId]

\* Next operator for IBCTransferReceivePacket
IBCTransferReceivePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            targetChain == chains[packet.targetChainId]
            IN
            /\ IBCTransferReceivePacketCondition(packet, targetChain)
            /\ chains' = [chains EXCEPT
                    ![packet.targetChainId] = IBCTransferReceivePacket(packet)
                ]
            /\ action' = [
                    name |-> IBCTransferReceivePacketAction,
                    packet |-> packet
                ]
            /\ outcome' = [name |-> SuccessOutcome]
            /\ UNCHANGED relayerRunning


\* Picks an IBCPacket from sourceChain to timeout
\* Refunds balance to source account
\* Moves the packet from pending to expired
\* @type: (PACKET) => CHAIN;
IBCTransferTimeoutPacket(packet) ==
    LET
    from == packet.from
    denom == packet.denom
    amount == packet.amount
    sourceChain == chains[packet.sourceChainId]
    targetChain == chains[packet.targetChainId]
    escrowAccount == sourceChain.escrow[packet.targetChainId]
    IN
    [
        sourceChain EXCEPT
        !.bank = [@ EXCEPT
            ![from] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ],
        !.escrow = [@ EXCEPT
            ![packet.targetChainId] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) - amount)
        ],
        !.localPackets = [@ EXCEPT
            !.pending = @ \ {packet.id},
            !.expired = @ \union {packet.id}
        ]
    ]

\* Checks if the packet is not processed by the targetChain
\* @type: (PACKET, CHAIN) => Bool;
IBCTransferTimeoutPacketCondition(packet, targetChain) ==
    /\ ~relayerRunning
    /\ packet.id \notin DOMAIN targetChain.remotePackets[packet.sourceChainId]

\* Next operator for IBCTransferTimeoutPacket
IBCTransferTimeoutPacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            sourceChain == chains[packet.sourceChainId]
            targetChain == chains[packet.targetChainId]
            IN
            /\ IBCTransferTimeoutPacketCondition(packet, targetChain)
            /\ chains' = [chains EXCEPT
                    ![sourceChain.id] = IBCTransferTimeoutPacket(packet)
                ]
            /\ action' = [
                    name |-> IBCTransferTimeoutPacketAction,
                    packet |-> packet
                ]
            /\ outcome' = [name |-> SuccessOutcome]
            /\ UNCHANGED relayerRunning


\* Mark an IBC packet at sourceChain as success which is processed at targetChain
\* @type: (PACKET) => CHAIN;
IBCTransferAcknowledgePacket(packet) ==
    LET sourceChain == chains[packet.sourceChainId] IN
    [
        sourceChain EXCEPT
        !.localPackets = [@ EXCEPT
            !.pending = @ \ {packet.id},
            !.success = @ \union {packet.id}
        ]
    ]

\* Checks if the packet is already processed by the targetChain
\* @type: (PACKET, CHAIN) => Bool;
IBCTransferAcknowledgePacketCondition(packet, targetChain) ==
    /\ relayerRunning
    /\ packet.sourceChainId \in DOMAIN targetChain.remotePackets
    /\ packet.id \in DOMAIN targetChain.remotePackets[packet.sourceChainId]

\* Next operator for IBCTransferAcknowledgePacket
IBCTransferAcknowledgePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            sourceChain == chains[packet.sourceChainId]
            targetChain == chains[packet.targetChainId]
            IN
            /\ IBCTransferAcknowledgePacketCondition(packet, targetChain)
            /\ chains' = [chains EXCEPT
                    ![sourceChain.id] = IBCTransferAcknowledgePacket(packet)
                ]
            /\ action' = [
                    name |-> IBCTransferAcknowledgePacketAction,
                    packet |-> packet
                ]
            /\ outcome' = [name |-> SuccessOutcome]
            /\ UNCHANGED relayerRunning

\* Init predicate
Init ==
    /\ chains = [chainId \in CHAIN_IDS |-> Genesis(chainId)]
    /\ relayerRunning = TRUE
    /\ action = [ name |-> NullAction ]
    /\ outcome = [ name |-> SuccessOutcome ]

\* Complete Next predicate
Next ==
    \/ LocalTransferNext
    \/ InterruptRelayNext
    \/ RestoreRelayNext
    \/ IBCTransferSendPacketNext
    \/ IBCTransferReceivePacketNext
    \/ IBCTransferTimeoutPacketNext
    \/ IBCTransferAcknowledgePacketNext

====
