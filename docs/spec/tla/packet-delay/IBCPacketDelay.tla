--------------------------- MODULE IBCPacketDelay ---------------------------

(***************************************************************************
 A TLA+ specification of the IBC packet transmission with packet delays. 
 Packet delays ensure that packet-related data should be accepted only 
 after some delay has passed since the corresponding header is installed. 
***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCPacketDelayDefinitions

CONSTANTS 
    \* @type: Int;
    MaxHeight, \* maximal height of all the chains in the system
    \* @type: Str;
    ChannelOrdering, \* indicate whether the channels are ordered or unordered
    \* @type: Int;
    MaxPacketSeq, \* maximal packet sequence number
    \* @type: Int;
    MaxDelay \* maximal packet delay

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
    \* @type: Str -> Seq(DATAGRAM);
    outgoingPacketDatagrams, \* packet datagrams created by the relayer but not submitted
    \* @type: Seq(LOGENTRY);
    packetLog, \* packet log
    \* @type: Int;
    appPacketSeqChainA, \* packet sequence number from the application on ChainA
    \* @type: Int;
    appPacketSeqChainB, \* packet sequence number from the application on ChainB
    \* @type: <<Str, Int>> -> Int;
    packetDatagramTimestamp \* history variable that tracks when packet datagrams were processed
           
chainAvars == <<chainAstore, packetDatagramsChainA, appPacketSeqChainA>>
chainBvars == <<chainBstore, packetDatagramsChainB, appPacketSeqChainB>>
vars == <<chainAstore, chainBstore,
          packetDatagramsChainA, packetDatagramsChainB,
          outgoingPacketDatagrams, packetLog, 
          appPacketSeqChainA, appPacketSeqChainB,
          packetDatagramTimestamp>>
          
Heights == 1..MaxHeight

(***************************************************************************
 Instances of Chain
 ***************************************************************************)

\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingPacketDatagrams <- packetDatagramsChainA,    
               appPacketSeq <- appPacketSeqChainA    

\* ChainB -- Instance of Chain.tla
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingPacketDatagrams <- packetDatagramsChainB,
               appPacketSeq <- appPacketSeqChainB         

 (***************************************************************************
 Environment operators
 ***************************************************************************)

\* get chain store by ID
\* @type: (Str) => CHAINSTORE;
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
               
\* update the client height of the client for the counterparty chain of chainID
UpdateClientHeights(chainID) ==
    /\ \/ /\ chainID = "chainA"
          /\ chainAstore.counterpartyClientHeights[chainBstore.height] = 0
          /\ chainAstore' = [chainAstore EXCEPT 
                              !.counterpartyClientHeights = [chainAstore.counterpartyClientHeights EXCEPT
                                ![chainBstore.height] = chainAstore.timestamp], 
                              !.timestamp = chainAstore.timestamp + 1
                            ]
          /\ UNCHANGED chainBstore
       \/ /\ chainID = "chainB"
          /\ chainBstore.counterpartyClientHeights[chainAstore.height] = 0  
          /\ chainBstore' = [chainBstore EXCEPT 
                              !.counterpartyClientHeights = [chainBstore.counterpartyClientHeights EXCEPT
                                ![chainAstore.height] = chainBstore.timestamp],
                              !.timestamp = chainBstore.timestamp + 1
                            ]
          /\ UNCHANGED chainAstore
       \/ UNCHANGED <<chainAstore, chainBstore>>
    /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>
    /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB, outgoingPacketDatagrams, packetLog>>


\* Compute a packet datagram designated for dstChainID, based on the packetLogEntry
\* @type: (Str, Str, LOGENTRY) => DATAGRAM;
PacketDatagram(srcChainID, dstChainID, packetLogEntry) ==
    
    LET srcChannelID == GetChannelID(srcChainID) IN \* "chanAtoB" (if srcChainID = "chainA")
    LET dstChannelID == GetChannelID(dstChainID) IN \* "chanBtoA" (if dstChainID = "chainB")
    
    LET srcPortID == GetPortID(srcChainID) IN \* "portA" (if srcChainID = "chainA")
    LET dstPortID == GetPortID(dstChainID) IN \* "portB" (if dstChainID = "chainB")
    
    LET srcHeight == GetLatestHeight(GetChainByID(srcChainID)) IN
    
    \* the source chain of the packet that is received by dstChainID is srcChainID
    LET recvPacket == [
                        sequence |-> packetLogEntry.sequence, 
                        timeoutHeight |-> packetLogEntry.timeoutHeight,
                        srcChannelID |-> srcChannelID,
                        srcPortID |-> srcPortID,
                        dstChannelID |-> dstChannelID,
                        dstPortID |-> dstPortID
                      ] IN
                                 
    \* the source chain of the packet that is acknowledged by srcChainID is dstChainID
    LET ackPacket == [
                        sequence |-> packetLogEntry.sequence, 
                        timeoutHeight |-> packetLogEntry.timeoutHeight,
                        srcChannelID |-> dstChannelID,
                        srcPortID |-> dstPortID,
                        dstChannelID |-> srcChannelID,
                        dstPortID |-> srcPortID
                     ] IN 
    
    IF packetLogEntry.type = "PacketSent"
    THEN [
            type |-> "PacketRecv",
            packet |-> recvPacket,  
            proofHeight |-> srcHeight
         ]
    ELSE IF packetLogEntry.type = "WriteAck"
         THEN [
                type |-> "PacketAck",
                packet |-> ackPacket,
                acknowledgement |-> packetLogEntry.acknowledgement,  
                proofHeight |-> srcHeight
              ]
         ELSE NullDatagram 
                        
\* submit a packet datagram if a delay has passed 
\* or install the appropriate height if it is missing
(* @type: (Str) => 
[
    datagramsChainA: Seq(DATAGRAM), datagramsChainB: Seq(DATAGRAM), 
    outgoingDatagrams: Str -> Seq(DATAGRAM), 
    chainA: CHAINSTORE, chainB: CHAINSTORE
];
*)
SubmitDatagramOrInstallClientHeight(chainID) == 
    LET packetDatagram == Head(outgoingPacketDatagrams[chainID]) IN
    LET chain == GetChainByID(chainID) IN
    
    \* if the proof height of the packet datagram is installed on the chain, 
    \* then clientHeightTimestamp is the timestamp, denoting the time when this 
    \* height was installed on the chain;
    \* otherwise it is 0, denoting that this height is not installed on the chain
    LET clientHeightTimestamp == chain.counterpartyClientHeights[packetDatagram.proofHeight] IN   
   
   \* packetDatagram.proof height is installed on chain  
   IF clientHeightTimestamp /= 0  
        \* the delay has passed
   THEN IF clientHeightTimestamp + MaxDelay < chain.timestamp
        \* submit the datagram to the corresponding chain
        THEN LET datagramsChainA == IF chainID = "chainA"
                                    THEN Append(packetDatagramsChainA, packetDatagram)
                                    ELSE packetDatagramsChainA IN
             LET datagramsChainB == IF chainID = "chainB"
                                    THEN Append(packetDatagramsChainB, packetDatagram)
                                    ELSE packetDatagramsChainB IN
             LET outgoingDatagrams == [outgoingPacketDatagrams EXCEPT 
                                        ![chainID] = Tail(outgoingPacketDatagrams[chainID])] IN
                                        
             [datagramsChainA |-> datagramsChainA,
              datagramsChainB |-> datagramsChainB,
              outgoingDatagrams |-> outgoingDatagrams,
              chainA |-> chainAstore,
              chainB |-> chainBstore] 
        \* the client height is installed, but the delay has not passed
        \* do not submit and do not install any new heights
        ELSE [datagramsChainA |-> packetDatagramsChainA,
              datagramsChainB |-> packetDatagramsChainB,
              outgoingDatagrams |-> outgoingPacketDatagrams,
              chainA |-> chainAstore,
              chainB |-> chainBstore]
   \* packetDatagram.proof height is not installed on chain, install it
   ELSE LET chainA == IF chainID = "chainA"
                      THEN [chainAstore EXCEPT 
                              !.counterpartyClientHeights = 
                                  [chainAstore.counterpartyClientHeights EXCEPT 
                                    ![packetDatagram.proofHeight] = chainAstore.timestamp],
                              !.timestamp = chainAstore.timestamp + 1
                            ]
                      ELSE chainAstore IN
        LET chainB == IF chainID = "chainB"
                      THEN [chainBstore EXCEPT 
                              !.counterpartyClientHeights = 
                                  [chainBstore.counterpartyClientHeights EXCEPT 
                                    ![packetDatagram.proofHeight] = chainBstore.timestamp],
                              !.timestamp = chainBstore.timestamp + 1
                            ]
                      ELSE chainBstore IN
                      
        [datagramsChainA |-> packetDatagramsChainA,
         datagramsChainB |-> packetDatagramsChainB,
         outgoingDatagrams |-> outgoingPacketDatagrams,
         chainA |-> chainA,
         chainB |-> chainB] 
         
(***************************************************************************
 Environment actions
 ***************************************************************************)
 \* update the client height of some chain
 UpdateClients ==
    \E chainID \in ChainIDs : UpdateClientHeights(chainID) 
 
\* create datagrams depending on packet log
CreateDatagrams ==
    /\ packetLog /= <<>>
    /\ LET packetLogEntry == Head(packetLog) IN
       LET srcChainID == packetLogEntry.srcChainID IN
       LET dstChainID == GetCounterpartyChainID(srcChainID) IN
       LET packetDatagram == PacketDatagram(srcChainID, dstChainID, packetLogEntry) IN
        /\ \/ /\ packetDatagram = NullDatagram
              /\ UNCHANGED outgoingPacketDatagrams
           \/ /\ packetDatagram /= NullDatagram 
              /\ outgoingPacketDatagrams' = 
                        [chainID \in ChainIDs |-> 
                            IF chainID = dstChainID
                            THEN Append(outgoingPacketDatagrams[chainID], packetDatagram)  
                            ELSE outgoingPacketDatagrams[chainID]
                        ]        
        /\ packetLog' = Tail(packetLog)    
        /\ UNCHANGED <<chainAstore, chainBstore>>
        /\ UNCHANGED <<packetDatagramsChainA, packetDatagramsChainB>>
        /\ UNCHANGED <<appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>

\* submit datagrams if delay has passed
SubmitDatagramsWithDelay ==
    \E chainID \in ChainIDs : 
        /\ outgoingPacketDatagrams[chainID] /= <<>>
        /\ LET submitted == SubmitDatagramOrInstallClientHeight(chainID) IN
            /\ packetDatagramsChainA' = submitted.datagramsChainA
            /\ packetDatagramsChainB' = submitted.datagramsChainB
            /\ outgoingPacketDatagrams' = submitted.outgoingDatagrams
            /\ chainAstore' = submitted.chainA
            /\ chainBstore' = submitted.chainB
            /\ UNCHANGED <<packetLog, appPacketSeqChainA, appPacketSeqChainB, packetDatagramTimestamp>>
        
(***************************************************************************
 Component actions
 ***************************************************************************)

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchange
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
       /\ UNCHANGED outgoingPacketDatagrams
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED outgoingPacketDatagrams

\* EnvironmentAction: either 
\*  - create packet datagrams if packet log is not empty, or
\*  - update counterparty clients, or
\*  - submit datagrams after their delay has passed
EnvironmentAction ==
    \/ CreateDatagrams    
    \/ UpdateClients
    \/ SubmitDatagramsWithDelay
    
(***************************************************************************
 Specification
 ***************************************************************************)    
               
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    /\ outgoingPacketDatagrams = [chainID \in ChainIDs |-> <<>>] 
    /\ packetLog = <<>>    
    /\ packetDatagramTimestamp = [<<chainID, h>> \in ChainIDs \X Heights |-> 0]
    
\* Next state action
Next ==
    \/ ChainAction
    \/ EnvironmentAction
    \/ UNCHANGED vars
    
Spec == Init /\ [][Next]_vars       

(***************************************************************************
 Invariants
 ***************************************************************************)

\* type invariant
TypeOK ==
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK
    /\ outgoingPacketDatagrams \in [ChainIDs -> Seq(Datagrams(Heights, MaxPacketSeq))]
    /\ packetDatagramTimestamp \in [ChainIDs \X Heights -> Int]   

\* each packet datagam is processed at time t (stored in packetDatagramTimestamp), 
\* such that t >= ht + delay, where 
\* ht is the time when the client height is installed  
PacketDatagramsDelay ==
    \A chainID \in ChainIDs : 
        \A h \in Heights :
            /\ GetChainByID(chainID).counterpartyClientHeights[h] /= 0
            /\ packetDatagramTimestamp[<<chainID, h>>] /= 0
            =>
            packetDatagramTimestamp[<<chainID, h>>] >= GetChainByID(chainID).counterpartyClientHeights[h] + MaxDelay

\* a conjunction of all invariants
Inv ==
    /\ PacketDatagramsDelay

=============================================================================
\* Modification History
\* Last modified Mon Apr 19 15:43:40 CEST 2021 by ilinastoilkovska
\* Created Thu Dec 10 13:44:21 CET 2020 by ilinastoilkovska
