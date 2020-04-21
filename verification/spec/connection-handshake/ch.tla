--------------------------------- MODULE CH ---------------------------------


VARIABLES
    parties,            \* The state of each party.
    inboundDatagrams    \* For each party, a buffer with any incoming datagrams. 


Parties == {"A", "B"}

ConnectionStates == { "UNINIT" }

Null == "none"

ConnectionIDs == {"connAtoB", "connBtoA"}


ClientIDs == { "clientA", "clientB" }


(***************************** ConnectionEnds *****************************
    Ref.: https://github.com/informalsystems/ibc-rs/pull/55.
    
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.
    
    - clientID -- a client identifier
      Stores the client identifier associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.
 ***************************************************************************)
ConnectionEnd ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {Null},
        clientID : ClientIDs \union {Null},
        counterpartyConnectionID : ConnectionIDs \union {Null},
        counterpartyClientID : ClientIDs \union {Null}
    ]      

(********************************** Helper functions
 ***************************************************************************)

\* Constructs a ConnectionEnd object for the given party in state UNINIT.
getConnectioEnd(targetParty) ==
    IF targetParty = "A"
    THEN 
        [   state |-> "UNINIT",
            connectionID |-> "connAtoB",
            clientID |-> "clientA",
            counterpartyConnectionID |-> "connBtoA",
            counterpartyClientID |-> "clientB" ]
    ELSE IF targetParty = "B"
         THEN
            [   state |-> "UNINIT",
                connectionID |-> "connBtoA",
                clientID |-> "clientB",
                counterpartyConnectionID |-> "connAtoB",
                counterpartyClientID |-> "clientA" ]
         ELSE Null    


\* Constructs a 'Init' Datagram.
\* Fields are hardcoded for the moment
getInitDatagram(targetParty) ==
    [ type |-> "ConnOpenInit", 
      connectionEnd |-> getConnectioEnd(targetParty) ]


isPartyInState(p, state) ==
    parties[p].connectionEnd.state = state


\* Would be ideal to import the following function.
\* Cf. ibc-rs#55 (file: ConnectionHandlers.tla)
getConnectionID(p) ==
    IF p = "A"
    THEN "connAtoB"
    ELSE IF p = "B"
         THEN "connBtoA"
         ELSE Null  


(********************************** Environment functions
 ***************************************************************************)

    
\* The environment generates the ConnOpenInit datagram, sending it to 'party'
GenerateConnOpenInit(targetParty) ==
    LET initDatagram == getInitDatagram(targetParty)
    IN inboundDatagrams' = [
                                inboundDatagrams EXCEPT
                                ![targetParty] = inboundDatagrams[targetParty] \union { initDatagram } 
                           ]
    /\ UNCHANGED <<parties>>


EnvStep ==
    \E targetParty \in Parties :
        GenerateConnOpenInit(targetParty)


(**************************** Party functions
 ***************************************************************************)

ConnectionEndInit ==
    [state |-> "UNINIT",
     connectionID |-> Null,
     clientID |-> Null,
     counterpartyConnectionID |-> Null,
     counterpartyClientID |-> Null ] 


(**
 * Connection Handshake Module handlers
 **)

CHModuleHandleInit(party) ==
    /\ isPartyInState(party, "UNINIT")
    /\  LET connOpenInitDgrs == {dgr \in inboundDatagrams[party] : 
                                /\ dgr.type = "ConnOpenInit"
                                /\ dgr.connectionID = getConnectionID(party)}
        IN IF connOpenInitDgrs /= {} 
           THEN LET connOpenInitDgr == CHOOSE dgr \in connOpenInitDgrs : TRUE 
                IN LET connOpenInitConnectionEnd == [
                     state |-> "INIT",
                     connectionID |-> connOpenInitDgr.connectionID,
                     clientID |-> connOpenInitDgr.clientID,
                     counterpartyConnectionID |-> connOpenInitDgr.counterpartyConnectionID,
                     counterpartyClientID |-> connOpenInitDgr.counterpartyClientID ] 
                  IN parties' = [ parties EXCEPT
                                        ![party] = [ connectionEnd |-> connOpenInitConnectionEnd ] 
                                    ]
                     /\ inboundDatagrams' = [ 
                                inboundDatagrams EXCEPT
                                ![party] = {} ]
           ELSE Null    \* TODO: no return value? unclear.


PartyInit ==
    [ connectionEnd |-> ConnectionEndInit ]

PartyStep ==
    \E party \in Parties :
        \/ CHModuleHandleInit(party)
    

(**************************** Main spec
 ***************************************************************************)


Init ==
    \* Associate to each party an initial state.
    /\ parties = [ p \in Parties |-> PartyInit ]
    /\ inboundDatagrams = [ p \in Parties |-> {} ]
    
Next == 
    \/ PartyStep
    \/ EnvStep

Spec ==
    Init /\ [][Next]_<<parties, inboundDatagrams>>


TypeInvariant ==
    /\ parties \in [ Parties -> { "UNINIT", "INIT", "TRYOPEN", "OPEN" } ]
\*    /\ inboundDatagrams \subseteq Datagrams

\* Model check it!
THEOREM Spec => []TypeInvariant


=============================================================================
\* Modification History
\* Last modified Tue Apr 21 19:17:35 CEST 2020 by adi
\* Created Fri Apr 17 10:28:22 CEST 2020 by adi

