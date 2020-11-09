-------------------------- MODULE ICS20Environment --------------------------

EXTENDS Integers, FiniteSets, Sequences, ICS20Definitions

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
          accounts \* a map from chainIDs and denominations to account balances

chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB>>
vars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA,
          chainBstore, packetDatagramsChainB, appPacketSeqChainB,
          packetLog, accounts>>
          
          
(***************************************************************************
 Instances of ICS20Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of ICS20Chain.tla
ChainA == INSTANCE ICS20Chain
          WITH ChainID <- "chainA",
               NativeDenomination <- NativeDenominationChainA,
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of ICS20Chain.tla
ChainB == INSTANCE ICS20Chain
          WITH ChainID <- "chainB",
               NativeDenomination <- NativeDenominationChainB,
               chainStore <- chainBstore,
               incomingPacketDatagrams <- packetDatagramsChainB,
               appPacketSeq <- appPacketSeqChainB

\* get chain store by ID
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
               
(***************************************************************************
 ICS02Environment actions
 ***************************************************************************)
\* Compute a packet datagram designated for dstChainID, based on the packetLogEntry
PacketDatagram(srcChainID, dstChainID, packetLogEntry) ==
    
    LET srcChannelID == GetChannelID(srcChainID) IN \* "chanAtoB" (if srcChainID = "chainA", dstChainID = "chainB")
    LET dstChannelID == GetChannelID(dstChainID) IN \* "chanBtoA" (if srcChainID = "chainA", dstChainID = "chainB")
    
    LET srcHeight == GetLatestHeight(GetChainByID(srcChainID)) IN
    
    \* the source chain of the packet that is received by dstChainID is srcChainID
    LET recvPacket(logEntry) == AsPacket([sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> srcChannelID,
                                 dstChannelID |-> dstChannelID,
                                 data |-> logEntry.data]) IN
                                 
    \* the source chain of the packet that is acknowledged by srcChainID is dstChainID
    LET ackPacket(logEntry) == AsPacket([sequence |-> logEntry.sequence, 
                                 timeoutHeight |-> logEntry.timeoutHeight,
                                 srcChannelID |-> dstChannelID,
                                 dstChannelID |-> srcChannelID,
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
 
 
\* create datagrams depending on packet log
CreateDatagrams ==
    LET packetLogEntry == Head(packetLog) IN
    LET srcChainID == packetLogEntry.srcChainID IN
    LET dstChainID == GetCounterpartyChainID(srcChainID) IN
    /\ \/ /\ srcChainID = "chainA"
          /\ packetDatagramsChainB' = 
                Append(packetDatagramsChainB, 
                       PacketDatagram(srcChainID, dstChainID, packetLogEntry))
          /\ UNCHANGED packetDatagramsChainA
       \/ /\ srcChainID = "chainB"
          /\ packetDatagramsChainA' = 
                Append(packetDatagramsChainA, 
                       PacketDatagram(srcChainID, dstChainID, packetLogEntry))
          /\ UNCHANGED packetDatagramsChainB
        
    /\ packetLog' = Tail(packetLog)    
    /\ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB>>
    /\ UNCHANGED accounts                       
    
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
    /\ packetLog /= AsPacketLog(<<>>)
    /\ CreateDatagrams    
    
(***************************************************************************
 Specification
 ***************************************************************************)    
               
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    /\ accounts = 
            [<<chainID, nativeDenom>> \in {<<"chainA", <<NativeDenominationChainA>>>>, 
                                           <<"chainB", <<NativeDenominationChainB>>>>} 
                                           |-> MaxBalance]  
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

=============================================================================
\* Modification History
\* Last modified Fri Nov 06 20:34:53 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:00:24 CEST 2020 by ilinastoilkovska
