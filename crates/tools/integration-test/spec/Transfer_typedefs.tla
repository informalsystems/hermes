---- MODULE Transfer_typedefs ----

(*
    @typeAlias: ACCOUNT_ID = Int;
    @typeAlias: CHAIN_ID = Int;
    @typeAlias: PACKET_ID = Int;

    TODO: Fix when to transfer back money to sink zone
    @typeAlias: DENOM_ID = CHAIN_ID;

    @typeAlias: PACKET = [
        id: PACKET_ID,
        from: ACCOUNT_ID,
        sourceChainId: CHAIN_ID,
        to: ACCOUNT_ID,
        targetChainId: CHAIN_ID,
        denom: DENOM_ID,
        amount: Int
    ];

    @typeAlias: BANK = DENOM_ID -> Int;

    @typeAlias: CHAIN = [
        id: CHAIN_ID,

        bank: ACCOUNT_ID -> BANK,
        supply: BANK,

        localPackets: [
            list: PACKET_ID -> PACKET,
            pending: Set(PACKET_ID),
            expired: Set(PACKET_ID),
            success: Set(PACKET_ID)
        ],

        remotePackets: CHAIN_ID -> PACKET_ID -> PACKET,

        escrow: CHAIN_ID -> BANK,

        nextPacketId: PACKET_ID
    ];
*)
typedefs == TRUE

====
