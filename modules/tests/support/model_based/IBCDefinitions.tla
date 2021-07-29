--------------------------- MODULE IBCDefinitions -----------------------------

EXTENDS Integers, FiniteSets, TLC

(********************** TYPE ANNOTATIONS FOR APALACHE ************************)
\* operator for type annotations
a <: b == a

ActionType == [
    type |-> STRING,
    chainId |-> STRING,
    clientState |-> Int,
    consensusState |-> Int,
    clientId |-> Int,
    header |-> <<Int, Int>>,
    previousConnectionId |-> Int,
    counterpartyChainId |-> STRING,
    counterpartyClientId |-> Int,
    counterpartyConnectionId |-> Int
]
AsAction(a) == a <: ActionType
AsSetAction(S) == S <: {ActionType}
AsSetInt(S) == S <: {Int}
(******************* END OF TYPE ANNOTATIONS FOR APALACHE ********************)

(******************************** Utils **************************************)
\* This is an implementation of the height comparison for Tendermint heights,
\* which include a revision (client version) and a block height.
\* - If height x's revision is higher than y's, x is higher.
\* - If x's revision is lower than y's, x is lower
\* - If x and y's revision's are equal, then we look at the block number
\* - - If x's block number is higher, x is higher.
\* - - If x's block number is lower, x is lower.
\* - - If x and y have the same revision and block number, the heights are equal.
HeightLT(a, b) ==
    \/ a[1] < b[1]
    \/ (a[1] = b[1] /\ a[2] < b[2])

HeightLTE(a, b) ==
    \/ a[1] < b[1]
    \/ (a[1] = b[1] /\ a[2] < b[2])
    \/ a = b

HeightGT(a, b) ==
    \/ a[1] > b[1]
    \/ (a[1] = b[1] /\ a[2] > b[2])

HeightGTE(a, b) ==
    \/ a[1] > b[1]
    \/ (a[1] = b[1] /\ a[2] > b[2])
    \/ a = b

\* Checks if the block is higher but the revision is the same
HigherBlock(a, b) ==
    /\ a[1] = b[1]
    /\ a[2] > b[2]

\* Checks if the revision is higher
HigherRevision(a, b) ==
    /\ a[1] > b[1]

Max(S) == CHOOSE x \in S: \A y \in S: y <= x
FindMaxHeight(S) == CHOOSE x \in S: \A y \in S: HeightLTE(y, x)

(*****************************************************************************)

\* if a chain identifier is not set then it is "-1"
ChainIdNone == "-1"
\* if a client identifier is not set then it is -1
ClientIdNone == -1
\* if a connection identifier is not set then it is -1
ConnectionIdNone == -1

===============================================================================
