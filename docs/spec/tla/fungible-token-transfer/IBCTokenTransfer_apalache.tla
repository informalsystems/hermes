--------------------- MODULE IBCTokenTransfer_apalache ---------------------

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          packetDatagramsChainA, \* set of packet datagrams incoming to ChainA
          packetDatagramsChainB, \* set of packet datagrams incoming to ChainB
          packetLog, \* packet log
          appPacketSeqChainA, \* packet sequence number from the application on ChainA
          appPacketSeqChainB, \* packet sequence number from the application on ChainB
          accounts, \* a map from chainIDs and denominations to account balances
          escrowAccounts \* a map from channelIDs and denominations to escrow account balances
          
INSTANCE IBCTokenTransfer WITH
    MaxHeight <- 2, 
    MaxPacketSeq <- 1, 
    MaxBalance <- 1,
    NativeDenominationChainA <- "atom", 
    NativeDenominationChainB <- "eth" 

=============================================================================
\* Modification History
\* Last modified Mon Feb 01 12:48:51 CET 2021 by ilinastoilkovska
\* Created Mon Feb 01 12:47:18 CET 2021 by ilinastoilkovska
