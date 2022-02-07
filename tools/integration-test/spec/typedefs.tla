---- MODULE typedefs ----

(*
    @typeAlias: PORT_ID = Str;
    @typeAlias: CHANNEL_ID = Int;
    @typeAlias: ACCOUNT_ID = Int;
    @typeAlias: CHAIN_ID = Str;
    @typeAlias: PACKET_ID = Int;

    TODO: Fix when to transfer back money to sink zone
    @typeAlias: DENOM_ID = Str;

    @typeAlias: CHANNEL_ENDPOINT = [
        chainId: CHAIN_ID,
        portId: PORT_ID,
        channelId: CHANNEL_ID
    ];

    @typeAlias: CHANNEL = [
        source: CHANNEL_ENDPOINT,
        target: CHANNEL_ENDPOINT
    ];

    @typeAlias: PACKET = [
        id: PACKET_ID,
        channel: CHANNEL,
        from: ACCOUNT_ID,
        to: ACCOUNT_ID,
        denom: DENOM_ID,
        amount: Int
    ];

    @typeAlias: BANK = DENOM_ID -> Int;

    @typeAlias: CHAIN = [
        id: CHAIN_ID,

        ports: Set(PORT_ID),
        channel: CHANNEL_ID -> CHANNEL,
        activeChannels: Set(CHANNEL_ID),

        bank: ACCOUNT_ID -> BANK,
        supply: BANK,

        localPackets: [
            list: PACKET_ID -> PACKET,
            pending: Set(PACKET_ID),
            expired: Set(PACKET_ID),
            success: Set(PACKET_ID)
        ],

        remotePackets: CHANNEL_ID -> PACKET_ID -> PACKET,

        ics20: [
            portId: PORT_ID,
            escrow: CHANNEL_ID -> ACCOUNT_ID,
            channel: CHAIN_ID -> CHANNEL_ID
        ],

        nextChannelId: CHANNEL_ID,
        nextPacketId: PACKET_ID,
        nextAccountId: ACCOUNT_ID
    ];
*)
typedefs == TRUE


====