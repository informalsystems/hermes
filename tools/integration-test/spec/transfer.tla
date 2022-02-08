---- MODULE transfer ----
EXTENDS TLC, Sequences, Integers, typedefs

CONSTANTS
    \* Set of blockchain names
    \* @type: Set(CHAIN_ID);
    CHAIN_IDS,
    \* Number of accounts per blockchain
    \* @type: ACCOUNT_ID;
    N_INITIAL_ACCOUNTS,
    \* Port ID used for ICS20
    \* @type: PORT_ID;
    ICS20_PORT,
    \* Genesis balance per account
    \* @type: Int;
    GENESIS_AMOUNT

VARIABLES
    \* Interchain state
    \* @type: CHAIN_ID -> CHAIN;
    chains,
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
CreateChannelAction == "CreateChannel"
IBCTransferSendPacketAction == "IBCTransferSendPacket"
IBCTransferReceivePacketAction == "IBCTransferReceivePacket"
IBCTransferAcknowledgePacketAction == "IBCTransferAcknowledgePacket"
IBCTransferTimeoutPacketAction == "IBCTransferTimeoutPacket"
ExpireChannelAction == "ExpireChannel"

\* Outcomes
SuccessOutcome == "Success"
ErrorOutcome == "Error"

\* Dummy operators for empty types

DummyAccount == 0

\* @type: () => CHANNEL_ENDPOINT;
DummyEndpoint == [
    chainId |-> 0,
    portId |-> "dummyPort",
    channelId |-> 0
]

\* @type: () => CHANNEL;
DummyChannel == [
    source |-> DummyEndpoint,
    target |-> DummyEndpoint
]

\* @type: () => PACKET;
DummyPacket == [
    id |-> 0
]

\* @type: (CHAIN_ID) => CHAIN;
Genesis(chainId) ==
    LET nativeDenom == chainId IN [
    \* Name of the chain
    id |-> chainId,
    \* Ports available for this chain
    ports |-> {ICS20_PORT},
    \* All the created channels in this chain
    channel |-> [channelId \in {} |-> DummyChannel],
    \* Active channels for this channel
    \* A pair of chain has maximum of one active channel
    activeChannels |-> {},

    \* Bank data for this chain
    \* To support different cross-chain(ibc) denoms, it is a 2D map.
    \* `accountId` has `bank[accountId][denomId]` many `denomId`.
    bank |-> [accountId \in ACCOUNT_IDS |-> [denom \in {nativeDenom} |-> GENESIS_AMOUNT]],
    \* Record of circulating native and cross-chain(ibc) token sourced at this chain
    supply |-> [denom \in {nativeDenom} |-> GENESIS_AMOUNT * N_INITIAL_ACCOUNTS ],

    \* Record of packets originated from this chain
    localPackets |-> [
        \* A table of packets with packetId
        list |-> [packetId \in {} |-> DummyPacket],
        \* Set of packetIds of packets which are not yet acknowledged by destination chain
        pending |-> {},
        \* Set of packetIds of packets which are not delivered to destrination chain within timeout block height
        expired |-> {},
        \* Set of packetIds of packets which are acknowledged by destination chain
        success |-> {}
    ],

    \* Record of packets receiveed from other chains
    \* Packets are maintained using the channelId, it was received at.
    \* Note: A pair of chain may have multiple channels in the past.
    remotePackets |-> [channelId \in {} |-> [packetId \in {} |-> DummyPacket]],

    \* ICS20 module keeper
    ics20 |-> [
        \* ICS20 Port ID
        portId |-> ICS20_PORT,
        \* Escrow accountId per channelId
        escrow |-> [channelId \in {} |-> DummyAccount],
        \* ID of the channel between this chain and chainId
        channel |-> [targetChainId \in {} |-> 0]
    ],

    \* track new IDs
    nextChannelId |-> 0,
    nextPacketId |-> 0,
    \* Used up first few accountIds already
    nextAccountId |-> N_INITIAL_ACCOUNTS + 1
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

CreateChannel                : create a channel
ExpireChannel                : a channel can expire

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
                        chain |-> chainId,
                        source |-> source,
                        target |-> target,
                        denom |-> denom,
                        amount |-> amount
                    ]
                /\ outcome' = [ name |-> SuccessOutcome ]

\* Checks if there exists an active channel between a pair of chains
\* @type: (CHAIN_ID, CHAIN_ID) => Bool;
ExistsChannelBetween(chain1Id, chain2Id) ==
    LET
    chain1 == chains[chain1Id]
    chain2 == chains[chain2Id]
    IN
    /\ chain2Id \in DOMAIN chain1.ics20.channel
    /\ chain1Id \in DOMAIN chain2.ics20.channel
    /\
        LET
        channelId1 == chain1.ics20.channel[chain2Id]
        channelId2 == chain2.ics20.channel[chain1Id]
        IN
        /\ channelId1 \in chain1.activeChannels
        /\ channelId2 \in chain2.activeChannels

\* Updates the sourceChain with a channel towards targetChain
\* @type: (CHAIN, CHAIN) => CHAIN;
AddICS20Channel(sourceChain, targetChain) ==
    LET
    sourceChannelId == sourceChain.nextChannelId
    targetChannelId == targetChain.nextChannelId
    sourceEndPoint == [chainId |-> sourceChain.id, portId |-> sourceChain.ics20.portId, channelId |-> sourceChannelId]
    targetEndPoint == [chainId |-> targetChain.id, portId |-> targetChain.ics20.portId, channelId |-> targetChannelId]
    escrowAccount == sourceChain.nextAccountId
    sourceChainDenom == sourceChain.id
    IN
    [
        sourceChain EXCEPT
        !.activeChannels = @ \union {sourceChannelId},
        !.channel = [
            x \in {sourceChannelId} \union DOMAIN @ |->
            IF x = sourceChannelId THEN [source |-> sourceEndPoint, target |-> targetEndPoint]
            ELSE @[x]
        ],
        !.remotePackets = AddOrUpdateEntry(@, sourceChannelId, [p \in {} |-> DummyPacket]),
        !.ics20 = [@ EXCEPT
            !.escrow = AddOrUpdateEntry(@, sourceChannelId, escrowAccount),
            !.channel = AddOrUpdateEntry(@, targetChain.id, sourceChannelId)
        ],
        !.bank = AddOrUpdateEntry(@, escrowAccount, [d \in {sourceChainDenom} |-> 0]),
        !.nextChannelId = @ + 1,
        !.nextAccountId = @ + 1
    ]

\* Next operator for CreateChannel
\* Creates a channel between a pair of chains
\* @type: () => Bool;
CreateChannelNext ==
    \E id1, id2 \in DOMAIN chains:
        /\ id1 /= id2
        /\ ~ExistsChannelBetween(id1, id2)
        /\ chains' = [
                chains EXCEPT
                ![id1] = AddICS20Channel(@, chains[id2]),
                ![id2] = AddICS20Channel(@, chains[id1])
            ]
        /\ action' = [
                name |-> CreateChannelAction,
                chains |-> {id1,id2}
            ]
        /\ outcome' = [ name |-> SuccessOutcome]

\* Expire a channel, at sourceChain, towards targetChain
\* @type: (CHAIN, CHAIN) => CHAIN;
ExpireChannel(sourceChain, targetChain) ==
    [
        sourceChain EXCEPT
        !.activeChannels = @ \ {sourceChain.ics20.channel[targetChain.id]}
    ]

\* Expires the channel between a pair of chains
\* Note: there exists maximum of one channel per pair of chains
\* Next operator for ExpireChannel
ExpireChannelNext ==
    \E id1, id2 \in DOMAIN chains:
        /\ id1 /= id2
        /\ ExistsChannelBetween(id1, id2)
        /\ chains' = [
                chains EXCEPT
                ![id1] = ExpireChannel(@, chains[id2]),
                ![id2] = ExpireChannel(@, chains[id1])
            ]
        /\ action' = [
                name |-> ExpireChannelAction,
                chains |-> {id1,id2}
            ]
        /\ outcome' = [ name |-> SuccessOutcome]

\* Checks if there exists a channel between two chains
\* @type: (CHAIN, CHAIN) => Bool;
IBCTransferSendPacketCondition(sourceChain, targetChain) ==
    /\ targetChain.id \in DOMAIN sourceChain.ics20.channel
    /\ sourceChain.ics20.channel[targetChain.id] \in sourceChain.activeChannels

\* Creates an IBCPacket with the necessary information and adds it to pending packets
\* @type: (CHAIN, ACCOUNT_ID, CHAIN, ACCOUNT_ID, DENOM_ID, Int) => CHAIN;
IBCTransferSendPacket(sourceChain, source, targetChain, target, denom, amount) ==
    LET
    channelId == sourceChain.ics20.channel[targetChain.id]
    escrowAccount == sourceChain.ics20.escrow[channelId]
    IN
    [
        sourceChain EXCEPT
        !.bank = [@ EXCEPT
            ![source] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) - amount),
            ![escrowAccount] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ],
        !.localPackets = [@ EXCEPT
            !.list = AddOrUpdateEntry(@,
                sourceChain.nextPacketId,
                [
                    id |-> sourceChain.nextPacketId,
                    channel |-> sourceChain.channel[channelId],
                    from |-> source,
                    to |-> target,
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
                    /\ IBCTransferSendPacketCondition(chains[chainId1], chains[chainId2])
                    /\ HasEnoughBalance(chains[chainId1], acc1, denom, amount)
                    /\ chains' = [chains EXCEPT
                            ![chainId1] = IBCTransferSendPacket(chains[chainId1], acc1, chains[chainId2], acc2, denom, amount)
                        ]
                    /\ action' = [
                            name |-> IBCTransferSendPacketAction,
                            packet |-> chains'[chainId1].localPackets.list[chains[chainId1].nextPacketId]
                        ]
                    /\ outcome' = [name |-> SuccessOutcome]

\* TODO:
\*  append CHANNEL_ID/PORT_ID for source zone
\*  trim CHANNEL_ID/PORT_ID for sink zone
\* @type: (DENOM_ID, CHANNEL) => DENOM_ID;
TransformDenom(denom, channel) ==
    denom

\* Process an IBC packet at targetChain
\* @type: (PACKET) => CHAIN;
IBCTransferReceivePacket(packet) ==
    LET
    channel == packet.channel
    destination == packet.to
    denom == TransformDenom(packet.denom, channel)
    amount == packet.amount
    targetChain == chains[channel.target.chainId]
    IN
    [
        targetChain EXCEPT
        !.bank = [@ EXCEPT
            ![destination] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount)
        ],
        !.supply = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount),
        !.remotePackets = [@ EXCEPT
            ![channel.target.channelId] = AddOrUpdateEntry(@,
                packet.id,
                packet
            )
        ]
    ]

\* Checks if the packet is not processed by the targetChain
\* @type: (PACKET, CHAIN) => Bool;
IBCTransferReceiveOrTimeoutPacketCondition(packet, targetChain) ==
    packet.id \notin DOMAIN targetChain.remotePackets[packet.channel.target.channelId]

\* Next operator for IBCTransferReceivePacket
IBCTransferReceivePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            targetChain == chains[packet.channel.target.chainId]
            IN
            /\ IBCTransferReceiveOrTimeoutPacketCondition(packet, targetChain)
            /\ chains' = [chains EXCEPT
                    ![targetChain.id] = IBCTransferReceivePacket(packet)
                ]
            /\ action' = [
                    name |-> IBCTransferReceivePacketAction,
                    packet |-> packet
                ]
            /\ outcome' = [name |-> SuccessOutcome]


\* Picks an IBCPacket from sourceChain to timeout
\* Refunds balance to source account
\* Moves the packet from pending to expired
\* @type: (PACKET) => CHAIN;
IBCTransferTimeoutPacket(packet) ==
    LET
    channel == packet.channel
    from == packet.from
    denom == packet.denom
    amount == packet.amount
    sourceChain == chains[channel.source.chainId]
    targetChain == chains[channel.target.chainId]
    channelId == sourceChain.ics20.channel[targetChain.id]
    escrowAccount == sourceChain.ics20.escrow[channelId]
    IN
    [
        sourceChain EXCEPT
        !.bank = [@ EXCEPT
            ![from] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) + amount),
            ![escrowAccount] = AddOrUpdateEntry(@, denom, GetDenomFromBank(@, denom) - amount)
        ],
        !.localPackets = [@ EXCEPT
            !.pending = @ \ {packet.id},
            !.expired = @ \union {packet.id}
        ]
    ]

\* Next operator for IBCTransferTimeoutPacket
IBCTransferTimeoutPacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            sourceChain == chains[packet.channel.source.chainId]
            targetChain == chains[packet.channel.target.chainId]
            IN
            /\ IBCTransferReceiveOrTimeoutPacketCondition(packet, targetChain)
            /\ chains' = [chains EXCEPT
                    ![sourceChain.id] = IBCTransferTimeoutPacket(packet)
                ]
            /\ action' = [
                    name |-> IBCTransferTimeoutPacketAction,
                    packet |-> packet
                ]
            /\ outcome' = [name |-> SuccessOutcome]


\* Mark an IBC packet at sourceChain as success which is processed at targetChain
\* @type: (PACKET) => CHAIN;
IBCTransferAcknowledgePacket(packet) ==
    LET sourceChain == chains[packet.channel.source.chainId] IN
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
    packet.id \in DOMAIN targetChain.remotePackets[packet.channel.target.channelId]

\* Next operator for IBCTransferAcknowledgePacket
IBCTransferAcknowledgePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET
            packet == chains[chainId].localPackets.list[packetId]
            sourceChain == chains[packet.channel.source.chainId]
            targetChain == chains[packet.channel.target.chainId]
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

\* Init predicate
Init ==
    /\ chains = [chainId \in CHAIN_IDS |-> Genesis(chainId)]
    /\ action = [ name |-> NullAction ]
    /\ outcome = [ name |-> SuccessOutcome ]

\* Complete Next predicate
Next ==
    \/ LocalTransferNext
    \/ CreateChannelNext
    \/ ExpireChannelNext
    \/ IBCTransferSendPacketNext
    \/ IBCTransferReceivePacketNext
    \/ IBCTransferTimeoutPacketNext
    \/ IBCTransferAcknowledgePacketNext

====