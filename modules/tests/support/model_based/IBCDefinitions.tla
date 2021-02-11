--------------------------- MODULE IBCDefinitions -----------------------------

EXTENDS Integers, FiniteSets

(********************** TYPE ANNOTATIONS FOR APALACHE ************************)
\* operator for type annotations
a <: b == a

ActionType == [
    type |-> STRING,
    chainId |-> STRING,
    clientState |-> Int,
    consensusState |-> Int,
    clientId |-> Int,
    header |-> Int,
    previousConnectionId |-> Int,
    counterpartyClientId |-> Int,
    counterpartyConnectionId |-> Int
]
AsAction(a) == a <: ActionType
AsSetInt(S) == S <: {Int}
(******************* END OF TYPE ANNOTATIONS FOR APALACHE ********************)

(******************************** Utils **************************************)
Max(S) == CHOOSE x \in S: \A y \in S: y <= x
(*****************************************************************************)

\* if a client identifier is not set then it is -1
ClientIdNone == -1
\* if a connection identifier is not set then it is -1
ConnectionIdNone == -1

===============================================================================
