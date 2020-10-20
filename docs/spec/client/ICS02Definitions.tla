-------------------------- MODULE ICS02Definitions --------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules, and which are relevant for ICS02
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* client state type
ClientStateType ==
    [
        clientID |-> STRING,
        heights |-> {Int}
    ]
    
\* chain store type 
ChainStoreType ==  
    [
        height |-> Int,
        clientStates |-> [Int -> ClientStateType]
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
        clientID |-> STRING
    ]

AsID(ID) == ID <: STRING
AsInt(n) == n <: Int
AsSetID(S) == S <: {STRING}
AsSetInt(S) == S <: {Int}
AsString(s) == s <: STRING

AsChainStore(chainStore) == chainStore <: ChainStoreType
AsClientState(clientState) == clientState <: ClientStateType

AsDatagram(dgr) == dgr <: DatagramType

AsClientDatagram(dgr) == dgr <: ClientDatagramType
AsSetClientDatagrams(Dgrs) == Dgrs <: {ClientDatagramType}

AsSetDatagrams(Dgrs) == Dgrs <: {DatagramType}
AsSeqDatagrams(Dgrs) == Dgrs <: Seq(DatagramType)

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 

nullHeight == 0
nullClientID == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 

BoundedSeq(S, bound) == UNION {[1..n -> S] : n \in 1..bound}

SetHeights(h1, h2) == {h \in 1..10 : h1 <= h /\ h <= h2}

(****************************** ClientStates *******************************
    A client state is a set of heights 
 ***************************************************************************)
ClientStates(ClientIDs, maxHeight) ==
    [
        clientID : ClientIDs,
        heights : SUBSET(1..maxHeight)
    ] <: ClientStateType
    
NullClientState ==
    [
        clientID |-> nullClientID,
        heights |-> AsSetInt({})
    ] <: ClientStateType    

(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS02. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.
      
 ***************************************************************************)
ChainStores(NrClients, ClientIDs, maxHeight) ==    
    [
        height : 1..maxHeight,
        clientStates : [1..NrClients -> ClientStates(ClientIDs, maxHeight)]
    ] <: {ChainStoreType}

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(ClientIDs, maxHeight) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : 1..maxHeight]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : 1..maxHeight]   
    <: {DatagramType}


(***************************** ClientDatagrams *****************************
 A set of client datagrams for a specific set ClIDs of client IDs.
 ***************************************************************************)
ClientDatagrams(ClientIDs, Heights) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : Heights]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : Heights]   
    <: {DatagramType}
    
NullDatagram == 
    [type |-> "null"] <: DatagramType    

(***************************************************************************
 Initial value of a chain store for ICS02
 ***************************************************************************)
\* Initial value of the chain store for ICS02: 
\*      - height is initialized to 1
\*      - the counterparty clients are uninitialized
ICS02InitChainStore(NrClients, ClientIDs) == 
    [
        height |-> AsInt(1),
        clientStates |-> [clientNr \in 1..NrClients |-> NullClientState]
    ] <: ChainStoreType
        
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")    
     
\* get the latest height of chainID
GetLatestHeight(chain) ==
    AsInt(chain.height)   

=========================================================================
\* Modification History
\* Last modified Mon Oct 19 18:35:08 CEST 2020 by ilinastoilkovska
\* Created Tue Oct 06 16:26:25 CEST 2020 by ilinastoilkovska
