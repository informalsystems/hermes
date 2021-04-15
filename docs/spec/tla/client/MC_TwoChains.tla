---------------------------- MODULE MC_TwoChains ----------------------------

MaxHeight == 4
NrClientsChainA == 2
NrClientsChainB == 2
ClientIDsChainA == {"B1", "B2"}
ClientIDsChainB == {"A1", "A2"}

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    \* @type: Set(DATAGRAM);
    datagramsChainA, \* set of datagrams incoming to ChainA
    \* @type: Set(DATAGRAM);
    datagramsChainB, \* set of datagrams incoming to ChainB
    \* @type: Str -> [created: Bool, updated: Bool];
    history \* history variable

INSTANCE ICS02TwoChainsEnvironment
=============================================================================