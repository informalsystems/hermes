------------------------- MODULE IBCTokenTransfer -------------------------

EXTENDS Integers, FiniteSets, Sequences, IBCTokenTransferDefinitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          MaxPacketSeq, \* maximal packet sequence number
          MaxBalance, \* maximal account balance
          NativeDenominationChainA, \* native denomination of tokens at ChainA
          NativeDenominationChainB \* native denomination of tokens at ChainA

VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          packetDatagramsChainA, \* set of packet datagrams incoming to ChainA
          packetDatagramsChainB, \* set of packet datagrams incoming to ChainB
          packetLog, \* packet log
          appPacketSeqChainA, \* packet sequence number from the application on ChainA
          appPacketSeqChainB, \* packet sequence number from the application on ChainB
          accounts, \* a map from chainIDs and denominations to account balances
          escrowAccounts \* a map from channelIDs and denominations to escrow account balances

chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB>>
vars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA,
          chainBstore, packetDatagramsChainB, appPacketSeqChainB,
          packetLog, accounts, escrowAccounts>>
          
          
(***************************************************************************
 Instances of ICS20Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               NativeDenomination <- NativeDenominationChainA,
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of Chain.tla
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               NativeDenomination <- NativeDenominationChainB,
               chainStore <- chainBstore,
               incomingPacketDatagrams <- packetDatagramsChainB,
               appPacketSeq <- appPacketSeqChainB

 (***************************************************************************
 ICS02Environment operators
 ***************************************************************************)

\* get chain store by ID
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
               
\* update the client height of the client for the counterparty chain of chainID
UpdateClientHeights(chainID) ==
    
    /\ \/ /\ chainID = "chainA"
          /\ chainAstore' = [chainAstore EXCEPT 
                            !.counterpartyClientHeights = 
                                chainAstore.counterpartyClientHeights 
                                \union 
                                {chainBstore.height}                          
                          ]
          /\ UNCHANGED chainBstore
       \/ /\ chainID = "chainB"
          /\ chainBstore' = [chainBstore EXCEPT 
                            !.counterpartyClientHeights = 
                                chainBstore.counterpartyClientHeights 
                                \union 
                                {chainAstore.height}                          
                          ]
          /\ UNCHANGED chainAstore
    /\ UNCHANGED <<accounts, escrowAccounts, appPacketSeqChainA, appPacketSeqChainB>>
    /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB, packetLog>>


\* Compute a packet datagram designated for dstChainID, based on the packetLogEntry
PacketDatagram(srcChainID, dstChainID, packetLogEntry) ==
    
    LET srcChannelID == GetChannelID(srcChainID) IN \* "chanAtoB" (if srcChainID = "chainA")
    LET dstChannelID == GetChannelID(dstChainID) IN \* "chanBtoA" (if dstChainID = "chainB")
    
    LET srcPortID == GetPortID(srcChainID) IN \* "portA" (if srcChainID = "chainA")
    LET dstPortID == GetPortID(dstChainID) IN \* "portb" (if dstChainID = "chainB")
    
    LET srcHeight == GetLatestHeight(GetChainByID(srcChainID)) IN
    
    \* the source chain of the packet that is received by dstChainID is srcChainID
    LET recvPacket(logEntry) == AsPacket([sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> srcChannelID,
                                 srcPortID |-> srcPortID,
                                 dstChannelID |-> dstChannelID,
                                 dstPortID |-> dstPortID,
                                 data |-> logEntry.data]) IN
                                 
    \* the source chain of the packet that is acknowledged by srcChainID is dstChainID
    LET ackPacket(logEntry) == AsPacket([sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> dstChannelID,
                                 srcPortID |-> dstPortID,
                                 dstChannelID |-> srcChannelID,
                                 dstPortID |-> srcPortID,
                                 data |-> logEntry.data]) IN                                 
    
    IF packetLogEntry.type = "PacketSent"
    THEN AsDatagram([type |-> "PacketRecv",
          packet |-> recvPacket(packetLogEntry),  
          proofHeight |-> srcHeight])
    ELSE IF packetLogEntry.type = "WriteAck"
         THEN AsDatagram([type |-> "PacketAck",
                  packet |-> ackPacket(packetLogEntry),
                  acknowledgement |-> packetLogEntry.acknowledgement,  
                  proofHeight |-> srcHeight])
         ELSE NullDatagram 
 
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
 \* update the client height of some chain
 UpdateClients ==
    \E chainID \in ChainIDs : UpdateClientHeights(chainID) 
 
\* create datagrams depending on packet log
CreateDatagrams ==
    /\ packetLog /= AsPacketLog(<<>>)
    /\ LET packetLogEntry == Head(packetLog) IN
       LET srcChainID == packetLogEntry.srcChainID IN
       LET dstChainID == GetCounterpartyChainID(srcChainID) IN
       LET packetDatagram == PacketDatagram(srcChainID, dstChainID, packetLogEntry) IN
        /\ \/ /\ packetDatagram = NullDatagram
              /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB>>
           \/ /\ packetDatagram /= NullDatagram 
              /\ srcChainID = "chainA"
              /\ packetDatagramsChainB' = 
                      Append(packetDatagramsChainB, packetDatagram)
              /\ UNCHANGED packetDatagramsChainA
           \/ /\ packetDatagram /= NullDatagram
              /\ srcChainID = "chainB"
              /\ packetDatagramsChainA' = 
                    Append(packetDatagramsChainA, 
                       PacketDatagram(srcChainID, dstChainID, packetLogEntry))
              /\ UNCHANGED packetDatagramsChainB
        
        /\ packetLog' = Tail(packetLog)    
        /\ UNCHANGED <<chainAstore, chainBstore>>
        /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB>>
        /\ UNCHANGED <<accounts, escrowAccounts>>                       
    
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchange
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars

\* EnvironmentAction: create packet datagrams if packet log is not empty       
EnvironmentAction ==
    \/ CreateDatagrams    
    \/ UpdateClients
    
(***************************************************************************
 Specification
 ***************************************************************************)    
               
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    \* bank accounts for each chain ID and its native denomination have MaxBalance
    /\ accounts = 
            [<<chainID, nativeDenom>> \in {<<"chainA", <<NativeDenominationChainA>>>>, 
                                           <<"chainB", <<NativeDenominationChainB>>>>} 
                                           |-> MaxBalance]  
    \* escrow accounts for each channel ID and the chain's native denomination have balance 0                                            
    /\ escrowAccounts = 
            [<<counterpartyChannelID, nativeDenom>> \in {<<"chanBtoA", <<NativeDenominationChainA>>>>, 
                                           <<"chanAtoB", <<NativeDenominationChainB>>>>} 
                                           |-> 0]
    /\ packetLog = AsPacketLog(<<>>)
    
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
\* fairness constraint    
Fairness ==
    /\ ChainA!Fairness
    /\ ChainB!Fairness
    /\ WF_vars(ChainAction)    
    
Spec == Init /\ [][Next]_vars /\ Fairness             

(***************************************************************************
 Helper operators used in properties and invariants
 ***************************************************************************)     

GetNativeDenomination(chainID) ==
    IF chainID = "chainA"
    THEN NativeDenominationChainA
    ELSE NativeDenominationChainB

\* compute sum over accounts that have chainID's native denomination
SumOverAllAccounts(chainID) ==
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    
    LET counterpartyChainID == GetCounterpartyChainID(chainID) IN
    LET channelID == GetChannelID(chainID) IN
    LET counterpartyPortID == GetCounterpartyPortID(chainID) IN
    LET counterpartyChannelID == GetCounterpartyChannelID(chainID) IN
    
    LET prefixedDenomination == <<counterpartyPortID, counterpartyChannelID, nativeDenomination>> IN
    
    IF <<counterpartyChainID, prefixedDenomination>> \in DOMAIN accounts
    THEN accounts[<<chainID, <<nativeDenomination>>>>] +
         accounts[<<counterpartyChainID, prefixedDenomination>>] + 
         escrowAccounts[<<counterpartyChannelID, <<nativeDenomination>>>>]
    ELSE accounts[<<chainID, <<nativeDenomination>>>>] +
         escrowAccounts[<<counterpartyChannelID, <<nativeDenomination>>>>]

(***************************************************************************
 Properties and invariants
 ***************************************************************************)

\* there are MaxAmount coins of each native denomination
PreservationOfTotalSupply ==
    \A chainID \in ChainIDs :
         SumOverAllAccounts(chainID) = MaxBalance

=============================================================================
\* Modification History
\* Last modified Fri Nov 20 12:23:23 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:00:24 CEST 2020 by ilinastoilkovska
