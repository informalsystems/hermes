-------------------------- MODULE ICS02Definitions --------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules, and which are relevant for ICS02
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* chain store type 
ChainStoreType == 
    [
        height |-> Int, 
        counterpartyClientHeights |-> {Int} 
    ]

\* client datagram type
ClientDatagramType ==
    [
        type |-> STRING,
        clientID |-> STRING,
        height |-> Int   
    ]

\* datagram type (record type containing fields of all datagrams)                  
DatagramType ==
    [
        type |-> STRING,
        height |-> Int,
        proofHeight |-> Int,
        consensusHeight |-> Int,
        clientID |-> STRING,
        counterpartyClientID |-> STRING
    ]

AsID(ID) == ID <: STRING
AsInt(n) == n <: Int
AsSetInt(S) == S <: {Int}
AsString(s) == s <: STRING

AsChainStore(chainStore) == chainStore <: ChainStoreType

AsDatagram(dgr) == dgr <: DatagramType

AsClientDatagram(dgr) == dgr <: ClientDatagramType
AsSetClientDatagrams(Dgrs) == Dgrs <: {ClientDatagramType}

AsSetDatagrams(Dgrs) == Dgrs <: {DatagramType}
AsSeqDatagrams(Dgrs) == Dgrs <: Seq(DatagramType)

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 
ClientIDs == {"clA", "clB"}

nullHeight == 0
nullClientID == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 

BoundedSeq(S, bound) == UNION {[1..n -> S] : n \in 1..bound}

(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS02. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.
      
 ***************************************************************************)
ChainStores(maxHeight) ==    
    [
        height : 1..maxHeight,
        counterpartyClientHeights : SUBSET(1..maxHeight)
    ] <: {ChainStoreType}

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(maxHeight) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : 1..maxHeight]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : 1..maxHeight]   
    <: {DatagramType}


(***************************** ClientDatagrams *****************************
 A set of client datagrams.
 ***************************************************************************)
ClientDatagrams(maxHeight, clID, h) ==
    [type : {"CreateClient"}, clientID : {clID}, height : h..maxHeight]
    \union
    [type : {"ClientUpdate"}, clientID : {clID}, height : h..maxHeight]   
    <: {ClientDatagramType}
    
NullDatagram == 
    [type |-> "null"] <: DatagramType    

(***************************************************************************
 Initial value of a chain store for ICS02
 ***************************************************************************)
\* Initial value of the chain store for ICS02: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
ICS02InitChainStore == 
    [
        height |-> 1,
        counterpartyClientHeights |-> AsSetInt({})
    ] <: ChainStoreType
        
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clA") ELSE AsID("clB")
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clB") ELSE AsID("clA")
    
\* get the latest height of chainID
GetLatestHeight(chain) ==
    AsInt(chain.height)   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= AsSetInt({})
    THEN AsInt(Max(chain.counterpartyClientHeights))
    ELSE AsInt(nullHeight)

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chain) ==
    AsSetInt(chain.counterpartyClientHeights)        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chain) ==
    AsInt(chain.counterpartyClientHeights) /= AsInt({})

\* returns true if the height h is in counterparty client heights on chainID 
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     

=============================================================================
\* Modification History
\* Last modified Wed Oct 07 12:15:39 CEST 2020 by ilinastoilkovska
\* Created Tue Oct 06 16:26:25 CEST 2020 by ilinastoilkovska
