----------------------------- MODULE ICS3Utils -----------------------------

(***************************************************************************

    This module is part of the TLA+ high-level specification for the
    IBC Connection Handshake protocol (ICS3).
    
    This module includes common action definitions that other modules need.

 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences


(* Obtain a set from the given sequence.
 *)    
SequenceAsSet(seq) ==
    {seq[x] : x \in DOMAIN seq}  


(* Checks if two version sequences overlap by taking the intersection of their 
    set representation.
 *)
VersionSequencesOverlap(versionSeq1, versionSeq2) ==
    SequenceAsSet(versionSeq1) 
     \intersect 
    SequenceAsSet(versionSeq2) /= {}


(* Checks if the versions of the two chain stores overlap; a wrapper over the
    base action 'VersionSequencesOverlap'.
 *)
ChainVersionsOverlap(chainStore, otherChainStore) ==
    VersionSequencesOverlap(chainStore.connection.version, otherChainStore.connection.version)


=============================================================================
\* Modification History
\* Last modified Thu Aug 27 16:02:28 CEST 2020 by adi
\* Created Thu Aug 27 15:39:01 CEST 2020 by adi
