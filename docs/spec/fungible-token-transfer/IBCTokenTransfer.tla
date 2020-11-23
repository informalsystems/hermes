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

RECURSIVE Sum(_)

Sum(S) ==
  IF S = AsSetInt({})
  THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN
    x + Sum(S \ {x})

GetNativeDenomination(chainID) ==
    IF chainID = "chainA"
    THEN NativeDenominationChainA
    ELSE NativeDenominationChainB
    
PrefixedDenoms(nativeDenomination) ==
    {<<portID, channelID, nativeDenomination>> : portID \in PortIDs, channelID \in ChannelIDs}    
    
EscrowAccountsDomain ==
    {<<GetCounterpartyChannelID(chainID), <<GetNativeDenomination(chainID)>>>> : 
            chainID \in ChainIDs}    
    
Denominations ==
    {<<NativeDenominationChainA>>, <<NativeDenominationChainB>>}
    \union
    PrefixedDenoms(NativeDenominationChainA) 
    \union 
    PrefixedDenoms(NativeDenominationChainB)
    
\* a packet is in flight if a packet commitment exists, but a 
\* corresponding packet receipt is not on the counterparty chain    
GetAmountsInFlight(chainID, nativeDenom) ==

    \* get packet commitments of chainID and packet receipts of its counterparty
    LET packetCommittments == GetChainByID(chainID).packetCommitments IN
    LET counterpartyChainID == GetCounterpartyChainID(chainID) IN
    LET counterpartyPacketReceipts == GetChainByID(counterpartyChainID).packetReceipts IN
    
    \* create expected packet receipt for a given packet commitment
    LET packetReceipt(packetCommitment) == 
        [channelID |-> GetCounterpartyChannelID(chainID),
         portID |-> GetCounterpartyPortID(chainID),
         sequence |-> packetCommitment.sequence] IN 
         
    \* get packet commitments for packets in flight
    LET inFlight == {pc \in packetCommittments : 
            packetReceipt(pc) \notin counterpartyPacketReceipts} IN
    
    \* get packet data for packets in flight
    LET inFlightData == {pc.data : pc \in inFlight} IN
    
    \* get packet data for packets in flight that have a prefixed denomination,
    \* where the last field is the native denomination of chainID
    LET inFlightDataOfDenomination == {d \in inFlightData : 
            d.denomination[Len(d.denomination)] = nativeDenom} IN
          
    \* compute set of amounts of the packets in flight that have 
    \* the desired denomination          
    {d.amount : d \in inFlightDataOfDenomination}
    
\* compute sum over accounts that have chainID's native denomination
SumOverLocalAccounts(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    \* get counterparty channel ID 
    LET counterpartyChannelID == GetCounterpartyChannelID(chainID) IN
        
    \* compute the sum over bank accounts and escrow accounts with 
    \* native denomination
    accounts[<<chainID, <<nativeDenomination>>>>] +
    escrowAccounts[<<counterpartyChannelID, <<nativeDenomination>>>>]

\* compute the sum over the amounts in escrow accounts
SumOverEscrowAccounts(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    
    \* get the escrow account IDs for the native denomination
    LET escrowAccountIDs == {<<channelID, <<nativeDenomination>>>> : channelID \in ChannelIDs} IN
    \* get the amounts in escrow accounts for the native denomination    
    LET escrowAccountAmounts == {escrowAccounts[accountID] : 
            accountID \in (escrowAccountIDs \intersect DOMAIN escrowAccounts)} IN
    
    \* compute the sum over the amounts in escrow accounts
    Sum(escrowAccountAmounts)

\* compute the sum over the amounts of packets in flight
SumOverPacketsInFlight(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN

    \* get the set of amounts of packets in flight for each chain
    LET amountsInFlight == UNION {GetAmountsInFlight(chID, nativeDenomination) : chID \in ChainIDs} IN
    
    \* compute the sum over the amounts of packets in flight
    Sum(amountsInFlight)

\* compute the sum over the amounts in bank accounts for prefixed denomination
SumOverBankAccountsWithPrefixedDenoms(chainID) ==
    \* get the native denomination of chainID
    LET nativeDenomination == GetNativeDenomination(chainID) IN
    
    \* compute the set of prefixed denominations
    LET prefixedDenominations == {pd \in PrefixedDenoms(nativeDenomination) : 
            /\ Len(pd) > 1
            /\ pd[Len(pd)] = nativeDenomination} IN

    \* get the bank account IDs for the prefixed denominations 
    LET accountIDs == {<<chID, prefixedDenomination>> : 
            chID \in ChainIDs, prefixedDenomination \in prefixedDenominations} IN 
               
    \* get the amounts in bank accounts for the prefixed denominations    
    LET accountAmounts == {accounts[accountID] : 
            accountID \in (accountIDs \intersect DOMAIN accounts)} IN
    
    \* compute the sum over the amounts in bank accounts
    Sum(accountAmounts)           

(***************************************************************************
 Properties and invariants
 ***************************************************************************)

\* there are MaxBalance coins of the native denomination in bank and escrow accounts 
\* for a given chain
PreservationOfTotalSupplyLocal ==
    \A chainID \in ChainIDs :
         SumOverLocalAccounts(chainID) = MaxBalance

\* The amount in nativeDenomination in escrow accounts 
\* is equal to the sum of:
\*    * the amounts in-flight packets in a (prefixed or unprefixed) denomination ending 
\*      nativeDenomination, and
\*    * the amounts in accounts in a prefixed denomination ending, 
\*      nativeDenomination, in which it is not native
PreservationOfTotalSupplyGlobal ==
    \A chainID \in ChainIDs : 
        SumOverEscrowAccounts(chainID) = 
            SumOverPacketsInFlight(chainID) + SumOverBankAccountsWithPrefixedDenoms(chainID)

\* a violation of this property is an execution where fungibility is preserved
NonPreservationOfFungibility ==
    \A accountID \in EscrowAccountsDomain :
        [](escrowAccounts[accountID] > 0 
            => [](escrowAccounts[accountID] > 0))
         
ICS20Inv ==
    /\ PreservationOfTotalSupplyLocal
    /\ PreservationOfTotalSupplyGlobal
    
ICS20Prop == 
    NonPreservationOfFungibility    

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 16:41:48 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:00:24 CEST 2020 by ilinastoilkovska
