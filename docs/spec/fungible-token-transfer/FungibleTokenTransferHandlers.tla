------------------- MODULE FungibleTokenTransferHandlers -------------------

EXTENDS Integers, FiniteSets, Sequences, Bank, ICS20Definitions

(***************************************************************************
 This module contains definitions of operators that are used to handle 
 ICS20 packet datagrams
 ***************************************************************************)

\* create outgoing packet data
\*      - accounts is the map of bank accounts
\*      - sender, receiver are chain IDs (used as addresses)
\*      - escrowAccounts is the map of escrow accounts of the chain that creates the packet
CreateOutgoingPacketData(accounts, escrowAccounts, denomination, amount, sender, receiver) ==
    \* sending chain is source if the denomination is of length 1  
    \* or if the denomination is not prefixed by the sender's channel ID  
    LET source == \/ Len(denomination) = 1
                  \/ Head(denomination) /= GetChannelID(sender) IN
    
    \* create packet data
    LET data ==
        [
            denomination |-> denomination,
            amount |-> amount,
            sender |-> sender,
            receiver |-> receiver
        ] IN  
    
    \* get the outcome of TransferCoins from the sender account to the escrow account
    LET transferCoinsOutcome ==   
            TransferCoins(accounts, sender, escrowAccounts, GetChannelID(sender), denomination, amount) IN
    
    \* get the outcome of BurnCoins applied to the sender account
    LET burnCoinsOutcome ==
            BurnCoins(accounts, sender, denomination, amount) IN 
            
    IF /\ source
       /\ ~transferCoinsOutcome.error
    \* if source and the coin transfer is successful, 
    \* update bank accounts and escrow accounts using the outcome from TransferCoins
    THEN [
            packetData |-> data,
            accounts |-> transferCoinsOutcome.senderAccounts, 
            escrowAccounts |-> transferCoinsOutcome.receiverAccounts,
            error |-> FALSE
         ]
    \* if not source and the coin burning is successful,
    \* update bank accounts using the outcome from BurnCoins
    ELSE IF /\ ~source
            /\ ~burnCoinsOutcome.error
         THEN [
                    packetData |-> data,
                    accounts |-> burnCoinsOutcome.accounts, 
                    escrowAccounts |-> escrowAccounts,
                    error |-> FALSE
              ]
         \* otherwise, there is an error
         ELSE [
                    packetData |-> data,
                    accounts |-> accounts, 
                    escrowAccounts |-> escrowAccounts,
                    error |-> TRUE
              ] 

\* receive an ICS20 packet
ICS20OnPacketRecv(chainID, chain, accounts, packet) ==
    \* get packet data and denomination
    LET data == packet.data IN
    LET denomination == data.denomination IN 
    
    LET escrowAccounts == chain.escrowAccounts IN
    
    \* receiving chain is source if 
    \* the denomination is prefixed by srcChannelID
    LET source == (Head(denomination) = packet.srcChannelID) IN
    
    LET unprefixedDenomination == Tail(denomination) IN
    LET prefixedDenomination == <<packet.dstChannelID>> \o denomination IN 
    
    \* get the outcome of TransferCoins from the escrow 
    \* to the receiver account
    LET transferCoinsOutcome ==   
            TransferCoins(
                escrowAccounts, packet.dstChannelID, 
                accounts, data.receiver, 
                unprefixedDenomination, data.amount
            ) IN
    
    \* get the outcome of MintCoins with prefixedDenomination 
    \* to the receiver account        
    LET mintCoinsOutcome ==
            MintCoins(
                accounts, data.receiver, 
                prefixedDenomination, data.amount
            ) IN             
    
    IF /\ source
       /\ ~transferCoinsOutcome.error
    \* if source and the coin transfer is successful, 
    \* update bank accounts and escrow accounts using the outcome from TransferCoins
    THEN 
        [
            packetAck |-> TRUE,
            accounts |-> transferCoinsOutcome.receiverAccounts, 
            escrowAccounts |-> transferCoinsOutcome.senderAccounts,
            error |-> FALSE
         ]
    \* if not source 
    \* update bank accounts using the outcome from MintCoins
    ELSE IF ~source
         THEN [ 
                packetAck |-> TRUE,
                accounts |-> mintCoinsOutcome,
                escrowAccounts |-> escrowAccounts,
                error |-> FALSE
              ]
         \* otherwise, there is an error
         ELSE [ 
                packetAck |-> FALSE,
                accounts |-> accounts,
                escrowAccounts |-> escrowAccounts,
                error |-> TRUE
              ]    
                
\* refund tokens on unsuccessful ack
RefundTokens(chainID, chain, accounts, packet) ==
\* should return a record with escrow, accounts 
    \* get packet data and denomination
    LET data == packet.data IN
    LET denomination == data.denomination IN
    
    LET escrowAccounts == chain.escrowAccounts IN
    
    \* chain is source if the denomination is of length 1  
    \* or if the denomination is not prefixed by srcChannelID  
    LET source == \/ Len(denomination) = 1
                  \/ Head(denomination) /= packet.srcChannelID IN
    
    \* get the outcome of TransferCoins from the escrow 
    \* to the sender account
    LET transferCoinsOutcome ==   
            TransferCoins(
                escrowAccounts, packet.srcChannelID, 
                accounts, data.sender, 
                denomination, data.amount
            ) IN
            
    \* get the outcome of MintCoins with denomination 
    \* to the sender account        
    LET mintCoinsOutcome ==
            MintCoins(
                accounts, data.sender, 
                denomination, data.amount
            ) IN   
            
    IF /\ source
       /\ ~transferCoinsOutcome.error
    \* if source and the coin transfer is successful, 
    \* update bank accounts and escrow accounts using the outcome from TransferCoins       
    THEN [
            accounts |-> transferCoinsOutcome.receiverAccounts, 
            escrowAccounts |-> transferCoinsOutcome.senderAccounts
         ]
    \* if not source 
    \* update bank accounts using the outcome from MintCoins         
    ELSE IF ~source
         THEN [
                accounts |-> mintCoinsOutcome, 
                escrowAccounts |-> escrowAccounts
              ]
         \* otherwise, do not update anything              
         ELSE [
                accounts |-> accounts, 
                escrowAccounts |-> escrowAccounts
              ]
    
\* acknowledge an ICS20 packet
ICS20OnPaketAck(chainID, chain, accounts, packet, ack) ==
    IF ~ack
    THEN RefundTokens(chainID, chain, accounts, packet)
    ELSE [
            accounts |-> accounts,
            escrowAccounts |-> chain.escrowAccounts
         ]
     

=============================================================================
\* Modification History
\* Last modified Fri Nov 06 16:46:45 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:02:01 CEST 2020 by ilinastoilkovska
