----------------------------- MODULE ICS3Types -----------------------------

(***************************************************************************

    This module is part of the TLA+ high-level specification for the
    IBC Connection Handshake protocol (ICS3).
    
    This module includes common domain definitions that other modules will
    extend.

 ***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANTS MaxHeight,
          AllConnectionIDs,
          AllClientIDs,
          AllChainIDs,
          AllVersionSeqs


(******************************* InitClients ********************************

     A set of records describing the possible initial values for the
     clients on a chain.
     
     A client record contains the following fields:

     - consensusHeights -- a set of heights 
       Stores the set of all heights (i.e., consensus states) that this
       client observed. At initialization time, the client only observes
       the first height, so the only possible value for this record is
       {1}.

     - clientID -- a string
       The identifier of the client. This is expected as a parameter, since
       it is a chain-specific field at initialization time.
       
     - latestHeight -- a number representing a (consensus) height
       Stores the latest height among all the heights in consensusHeights.
       Initialized to 1.

 ***************************************************************************)
InitClients(specificClientIDs) ==
    [
        consensusHeights : {{1}},
        clientID : specificClientIDs,
        latestHeight : {1}
    ]
    

(***************************** InitMsgs ***********************************

    The set of ConnectionHandshakeMessage records where message type is
    ICS3MsgInit.

    This operator returns the set of all initialization messages, such that
    the local end is the set 'le', and the remote end is set 're'.
 
 ***************************************************************************)
InitMsgs(le, re) ==
    [
        type : {"ICS3MsgInit"},
        parameters : [
                        localEnd : le,
                        remoteEnd : re
                     ]
    ]


(***************************** ICS3MessageTypes ****************************

    The set of valid message types that the ICS3Module can
    handle, e.g., as incoming or outgoing messages.

    In the low-level connection handshake protocol, the four messages have
    types: ConnOpenInit, ConnOpenTry, ConnOpenAck, ConnOpenConfirm.
    In this high-level specification, we choose slightly different names, to
    make an explicit distinction to the low-level protocol. Message types
    are as follows:
    ICS3MsgInit, ICS3MsgTry, ICS3MsgAck, and ICS3MsgConfirm.
    For a complete description of the message record, see
    ConnectionHandshakeMessage below.
     
 ***************************************************************************)
ICS3MessageTypes ==
    {
        "ICS3MsgInit", 
        "ICS3MsgTry",
        "ICS3MsgAck",
        "ICS3MsgConfirm"
    }


(******************************* ICS3ConnectionStates **********************

    The set of valid states that a connection can be in. 
     
 ***************************************************************************)
ICS3ConnectionStates == 
    {
        "UNINIT",
        "INIT", 
        "TRYOPEN",
        "OPEN"
     }


NullClientID ==
    "NULLClientID"

NullConnectionID ==
    "NULLConnectionID"


(******************************* NullConnectionEnd *************************

    A special record defining an uninitialized connection end record. 
     
 ***************************************************************************)
NullConnectionEnd ==
    [
        connectionID |-> NullConnectionID,
        clientID |-> NullClientID
    ]


(******************************* NullConnectionParameters ******************
 
    A record defining the special null connection parameters record.
     
 ***************************************************************************)
NullConnectionParameters == 
    [
        localEnd |-> NullConnectionEnd,
        remoteEnd |-> NullConnectionEnd
    ]


(******************************* ConnectionEnds *****************************
     
    A set of connection end records.
    A connection end record contains the following fields:
     
     - connectionID -- a string 
       Stores the identifier of this connection, specific to a chain.

     - clientID -- a string
       Stores the identifier of the client running on this chain.  
     
 ***************************************************************************)
ConnectionEnds ==
    [
        connectionID : AllConnectionIDs,
        clientID : AllClientIDs
    ]


(******************************* ConnectionParameters **********************

    A set of connection parameter records.
    A connection parameter record contains the following fields:

     - localEnd -- a connection end 
       Specifies the local connection details (i.e., connection ID and
       client ID).

     - remoteEnd -- a connection end
       Specifies the remote connection details.  

 ***************************************************************************)
ConnectionParameters ==
    [
        localEnd : ConnectionEnds,
        remoteEnd : ConnectionEnds
    ]
    \union
    { 
        NullConnectionParameters 
    }


(******************************* NullConnection ****************************

    Initially, the connection on both chains is uninitialized, defined as
    this special record. 
     
 ***************************************************************************)
NullConnections == [
    parameters : {NullConnectionParameters},
    state : {"UNINIT"},
    version : AllVersionSeqs \ {<<>>}
]


(******************************* Connections *******************************

     The set of possible connection records.
     A connection record contains the following fields:

     - parameters -- a connection parameters record 
       Specifies the local plus remote ends.

     - state -- a connection state (see ConnectionStates set).
     
 ***************************************************************************)
Connections ==
    [
        parameters : ConnectionParameters,
        state : ICS3ConnectionStates, 
        version : AllVersionSeqs
    ]


(******************************* ConnProof *********************************

     A set of records describing the possible values for connection proofs.

     A connection proof record contains a single field:

     - connection -- a connection record
       This is the connection (in the local store of a chain) at the moment
       when the module created this proof.

 ***************************************************************************)
ConnProofs ==
    [
        connection : Connections
    ]


(******************************* Heights ***********************************

     The set of all possible heights that a chain can assume throughout any
     execution.

 ***************************************************************************)
Heights ==
    1..MaxHeight


(******************************* ClientProofs *******************************

     A set of records describing the possible values for client proofs.
     
     A client proof record contains two fields:
     
     - latestHeight -- a number representing a height
     The current height (latestHeight) of the client (in the local store of a
     chain) at the moment when the ICS3 module created this proof. 

     - consensusHeights -- a set of heights
     The set of heights of the client colocated with module which created
     this proof.

 ***************************************************************************)
ClientProofs ==
    [
        latestHeight : Heights,
        consensusHeights : SUBSET Heights
    ]


(*********************** ConnectionHandshakeMessages ***********************

    The set of ConnectionHandshakeMessage records.
    These are connection handshake specific messages that two chains exchange
    while executing the ICS3 protocol.
 
 ***************************************************************************)
ConnectionHandshakeMessages ==
    [
        type : {"ICS3MsgInit"},
        parameters : ConnectionParameters
    ]
    \union
    [
        type : {"ICS3MsgTry"},
        parameters : ConnectionParameters,
        proofHeight : Heights,
        connProof : ConnProofs,
        clientProof : ClientProofs,
        version : AllVersionSeqs
    ]
    \union
    [
        type : {"ICS3MsgAck"},
        parameters : ConnectionParameters,
        proofHeight : Heights,
        connProof : ConnProofs,
        clientProof : ClientProofs,
        version : AllVersionSeqs
    ]
    \union
    [
        type : {"ICS3MsgConfirm"},
        parameters : ConnectionParameters,
        proofHeight : Heights,
        connProof : ConnProofs
    ]



(********************** MessageTypeIncludesConnProof ***********************

     Operator that evaluates to true if the message type (input parameter
     'type') refers to a message that includes a connection proof.

 ***************************************************************************)
MessageTypeIncludesConnProof(type) ==
    type \in {"ICS3MsgTry", "ICS3MsgAck", "ICS3MsgConfirm"}


(******************************* Clients ***********************************

     A set of records describing all the possible values for the
     clients on a chain.

     See client record description above (within the InitClients operator).

 ***************************************************************************)
Clients ==
    [
        consensusHeights : SUBSET Heights,
        clientID : AllClientIDs \union { NullClientID },
        latestHeight : Heights
    ]

(******************************* Stores *************************************

    The set of store records.
    A store record represents the local storage of a chain. This record
    contains the following fields:

     - chainID -- a string
       Stores the identifier of the chain where this module executes.

     - latestHeight -- a number representing a height
       Describes the current height of the chain.

     - connection -- a connection record
       Captures all the details of the connection on this chain.
       For a full description of a connection record, see the
       'Environment.Connections' set.

     - client -- a client record.
       Specifies the state of the client running on this chain.

 ***************************************************************************)   
Stores ==
    [
        chainID : AllChainIDs,
        latestHeight : Heights,
        connection : Connections \union NullConnections,
        client : Clients
    ]


=============================================================================
\* Modification History
\* Last modified Thu Aug 20 14:14:03 CEST 2020 by ilinastoilkovska
\* Last modified Tue Jun 23 13:47:17 CEST 2020 by adi
\* Created Mon May 18 17:53:08 CEST 2020 by adi

