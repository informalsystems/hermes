---- MODULE transfer ----
EXTENDS typedefs, Integers

CONSTANTS
    \* @type: Set(CHAIN_ID);
    CHAIN_IDS,
    \* @type: Set(ACCOUNT_ID);
    ACCOUNT_IDS,
    \* @type: PORT_ID;
    ICS20_PORT,
    \* @type: Int;
    TOTAL_SUPPLY

VARIABLES
    \* @type: CHAIN_ID -> CHAIN;
    chains,
    \* @type: [ name: Str ];
    action,
    \* @type: [ name: Str ];
    outcome

\* @type: () => Str;
NullAction == "Null"
\* @type: () => Str;
LocalTransferAction == "LocalTransfer"
\* @type: () => Str;
CreateChannelAction == "CreateChannel"
\* @type: () => Str;
IBCTransferSendPacketAction == "IBCTransferSendPacket"
\* @type: () => Str;
IBCTransferReceivePacketAction == "IBCTransferReceivePacket"
\* @type: () => Str;
IBCTransferAcknowledgePacketAction == "IBCTransferAcknowledgePacket"
\* @type: () => Str;
IBCTransferTimeoutPacketAction == "IBCTransferTimeoutPacket"
\* @type: () => Str;
ExpireChannelAction == "ExpireChannel"
\* @type: () => Str;
SuccessOutcome == "Success"
\* @type: () => Str;
ErrorOutcome == "Error"

\* @type: () => CHANNEL_ENDPOINT;
DummyEndpoint == [
    chainId |-> "dummyChain",
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
Genesis(chainId) == [
    id |-> chainId,
    ports |-> {ICS20_PORT},
    channel |-> [c \in {} |-> DummyChannel],
    activeChannels |-> {},

    bank |-> [a \in ACCOUNT_IDS \union {"reserve"} |-> [d \in {chainId} |-> IF a = "reserve" THEN TOTAL_SUPPLY ELSE 0]],
    supply |-> [d \in {chainId} |-> TOTAL_SUPPLY],

    localPackets |-> [
        list |-> [p \in {} |-> DummyPacket],
        pending |-> {},
        expired |-> {},
        success |-> {}
    ],

    remotePackets |-> [c \in {} |-> [p \in {} |-> DummyPacket]],
    
    ics20 |-> [
        portId |-> ICS20_PORT,
        escrow |-> [a \in {} |-> "DummyAccount"],
        channel |-> [c \in {} |-> 0]
    ],

    nextChannelId |-> 0,
    nextPacketId |-> 0
]

(*
LocalTransfer                : direct (created for airdrop)

CreateChannel                : create channel and add in activeChannel

IBCTransferSendPacket        : source; put in pending
IBCTransferReceivePacket     : target; put in received
IBCTransferAcknowledgePacket : source; put in successful

IBCTransferTimeoutPacket     : source; put in failed
ExpireChannel                : remove a channelId from activeChannel
*)

\* Checks if the source account has enough balance
\* @type: (CHAIN, ACCOUNT_ID, DENOM_ID, Int) => Bool;
HasBalance(chain, source, denom, amount) ==
    /\ source \in DOMAIN chain.bank
    /\ denom \in DOMAIN chain.bank[source]
    /\ chain.bank[source][denom] >= amount

\*  local bank after local 
\* @type: (CHAIN, ACCOUNT_ID, ACCOUNT_ID, DENOM_ID, Int) => CHAIN;
LocalTransfer(chain, source, target, denom, amount) ==
    [
        chain EXCEPT
        !.bank = [
            @ EXCEPT 
            ![source] = [@ EXCEPT ![denom] = @ - amount],
            ![target] = [@ EXCEPT ![denom] = @ + amount]
        ]
    ]

\* @type: () => Bool;
LocalTransferNext ==
    \E chainId \in CHAIN_IDS:
        \E source, target \in ACCOUNT_IDS \union {"reserve"}:
            \E amount \in 1..10:
                LET chain == chains[chainId] IN
                /\ HasBalance(chain, source, chain.id, amount)
                /\ chains' = [
                        chains EXCEPT 
                        ![chainId] = LocalTransfer(@, source, target, chain.id, amount)
                    ]
                /\ action' = [ name |-> LocalTransferAction ]
                /\ outcome' = [ name |-> SuccessOutcome ]

\* @type: (CHAIN_ID, CHAIN_ID) => Bool;
ExistsChannelBetween(chain1Id, chain2Id) ==
    LET chain1 == chains[chain1Id] IN 
    LET chain2 == chains[chain2Id] IN 
    /\ chain2Id \in DOMAIN chain1.ics20.channel
    /\ chain1Id \in DOMAIN chain2.ics20.channel
    /\ 
        LET channelId1 == chain1.ics20.channel[chain2Id] IN 
        LET channelId2 == chain2.ics20.channel[chain1Id] IN
        /\ channelId1 \in chain1.activeChannels
        /\ channelId2 \in chain2.activeChannels

\* @type: (CHAIN, CHAIN) => CHAIN;
AddICS20Channel(sourceChain, targetChain) ==
    LET sourceChannelId == sourceChain.nextChannelId IN 
    LET targetChannelId == targetChain.nextChannelId IN 
    LET sourceEndPoint == [chainId |-> sourceChain.id, portId |-> sourceChain.ics20.portId, channelId |-> sourceChannelId] IN
    LET targetEndPoint == [chainId |-> targetChain.id, portId |-> targetChain.ics20.portId, channelId |-> targetChannelId] IN
    [
        sourceChain EXCEPT 
        !.activeChannels = @ \union {sourceChannelId},
        !.channel = [@ EXCEPT
            ![sourceChannelId] = [source |-> sourceEndPoint, target |-> targetEndPoint]
        ],
        !.remotePackets = [@ EXCEPT ![targetChannelId] = [p \in {} |-> DummyPacket]],
        !.ics20 = [@ EXCEPT !.channels = [@ EXCEPT
            ![targetChain.id] = targetChannelId
        ]],
        !.nextChannelId = @ + 1
    ]

\* @type: () => Bool;
CreateChannelNext ==
    \E id1, id2 \in DOMAIN chains:
        /\ ~ExistsChannelBetween(id1, id2)
        /\ chains' = [
                chains EXCEPT
                ![id1] = AddICS20Channel(@, chains[id2]),
                ![id2] = AddICS20Channel(@, chains[id1])
            ]
        /\ action' = [ name |-> CreateChannelAction ]
        /\ outcome' = [ name |-> SuccessOutcome]

\* Checks if there exists a channel between two chains
\* @type: (CHAIN, CHAIN) => Bool;
IBCTransferSendPacketCondition(sourceChain, targetChain) ==
    /\ targetChain.id \in DOMAIN sourceChain.ics20.channel
    /\ sourceChain.ics20.channel[targetChain.id] \in sourceChain.activeChannels

\* @type: (CHAIN, ACCOUNT_ID, CHAIN, ACCOUNT_ID, DENOM_ID, Int) => CHAIN;
IBCTransferSendPacket(sourceChain, source, targetChain, target, denom, amount) ==
    LET channelId == sourceChain.ics20.channel[targetChain.id] IN
    LET escrowAccount == sourceChain.ics20.escrow[channelId] IN
    [
        sourceChain EXCEPT
        !.bank = [@ EXCEPT
            ![source] = [@ EXCEPT ![denom] = @ - amount],
            ![escrowAccount] = [@ EXCEPT ![denom] = @ + amount]
        ],
        !.localPackets = [@ EXCEPT
            !.list = [@ EXCEPT
                ![sourceChain.nextPacketId] = [
                    id |-> sourceChain.nextPacketId,
                    channel |-> sourceChain.channel[channelId],
                    from |-> source,
                    to |-> target,
                    denom |-> denom,
                    amount |-> amount
                ]
            ],
            !.pending = @ \union {sourceChain.nextPacketId}
        ],
        !.nextPacketId = @ + 1
    ]

IBCTransferSendPacketNext ==
    \E chainId1, chainId2 \in CHAIN_IDS:
        \E acc1, acc2 \in ACCOUNT_IDS:
            \E denom \in DOMAIN chains[chainId1].supply:
                \E amount \in 1..10:
                    /\ IBCTransferSendPacketCondition(chains[chainId1], chains[chainId2])
                    /\ HasBalance(chains[chainId1], acc1, denom, amount)
                    /\ chains' = [chains EXCEPT 
                            ![chainId1] = IBCTransferSendPacket(chains[chainId1], acc1, chains[chainId2], acc2, denom, amount)
                        ]
                    /\ action' = [name |-> IBCTransferSendPacketAction]
                    /\ outcome' = [name |-> SuccessOutcome]

\* TODO:
\*  append CHANNEL_ID/PORT_ID for source zone
\*  trim CHANNEL_ID/PORT_ID for sink zone
\* @type: (DENOM_ID, CHANNEL) => DENOM_ID;
TransformDenom(denom, channel) ==
    denom

\* @type: (PACKET) => CHAIN;
IBCTransferReceivePacket(packet) ==
    LET channel == packet.channel IN
    LET destination == packet.to IN
    LET denom == TransformDenom(packet.denom, channel) IN 
    LET amount == packet.amount IN
    LET sourceChain == chains[channel.source.chainId] IN
    LET targetChain == chains[channel.target.chainId] IN
    [
        targetChain EXCEPT
        !.bank = [@ EXCEPT
            ![destination] = [@ EXCEPT ![denom] = @ + amount]
        ],
        !.supply = [@ EXCEPT ![denom] = @ + amount],
        !.remotePackets = [@ EXCEPT 
            ![channel.target.channelId] = [@ EXCEPT 
                ![packet.id] = packet
            ]
        ]
    ]

IBCTransferReceivePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET packet == chains[chainId].localPackets.list[packetId] IN
            LET targetChain == chains[packet.channel.target.chainId] IN
            /\ chains' = [chains EXCEPT
                    ![targetChain.id] = IBCTransferReceivePacket(packet)
                ]
            /\ action' = [name |-> IBCTransferReceivePacketAction]
            /\ outcome' = [name |-> SuccessOutcome]


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

IBCTransferAcknowledgePacketNext ==
    \E chainId \in CHAIN_IDS:
        \E packetId \in chains[chainId].localPackets.pending:
            LET packet == chains[chainId].localPackets.list[packetId] IN
            LET targetChain == chains[packet.channel.target.chainId] IN
            /\ packetId \notin DOMAIN targetChain.remotePackets[packet.channel.target.channelId]
            /\ chains' = [chains EXCEPT 
                    ![packet.channel.source.chainId] = IBCTransferAcknowledgePacket(packet)
                ]
            /\ action' = [name |-> IBCTransferAcknowledgePacketAction]
            /\ outcome' = [name |-> SuccessOutcome]

Init ==
    /\ chains = [chainId \in CHAIN_IDS |-> Genesis(chainId)]
    /\ action = [ name |-> NullAction ]
    /\ outcome = [ name |-> SuccessOutcome ]

Next ==
    \/ LocalTransferNext
    \/ CreateChannelNext
    \* \/ ExpireChannelNext
    \/ IBCTransferSendPacketNext
    \/ IBCTransferReceivePacketNext
    \* \/ IBCTransferTimeoutPacketNext
    \/ IBCTransferAcknowledgePacketNext

====