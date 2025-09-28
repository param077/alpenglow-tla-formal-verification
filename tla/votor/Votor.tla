------------------------------- MODULE Votor -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

(************************************************************************)
(* PARAMETERS *)
(************************************************************************)
CONSTANTS
  Nodes,       \* set of validator ids
  Stake,       \* function: Node -> Natural (stake units)
  THRESH80,    \* integer stake units for 80% threshold
  THRESH60     \* integer stake units for 60% threshold

(************************************************************************)
(* simple summation helper (recursive) *)
(************************************************************************)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN f[x] + Sum(f, S \ {x})

TotalStake == Sum(Stake, Nodes)

(************************************************************************)
(* TYPES / SIMPLE HELPERS *)
(************************************************************************)
VoteType == {"Notar", "NotarFallback", "Final", "Skip", "SkipFallback", "None"}

(************************************************************************)
(* STATE *)
(************************************************************************)
CONSTANT Slots   \* finite set of slots to explore

VARIABLES
  votes,
  certs,
  pendingBlock

Init ==
  /\ votes = [s \in Slots |-> [v \in Nodes |-> "None"]]
  /\ certs = {}
  /\ pendingBlock = [s \in Slots |-> "NULL"]


(************************************************************************)
(* helper to compute stake for a set of nodes *)
(************************************************************************)
StakeOf(S) == Sum(Stake, S)

(************************************************************************)
(* When many nodes have Notar votes, build certificates *)
(************************************************************************)
BuildCerts(slot) ==
  LET
    block == pendingBlock[slot]
    notarStake ==
      IF block = "NULL" THEN 0
      ELSE StakeOf({ v \in Nodes : votes[slot][v] = "Notar" })
    finalStake ==
      IF block = "NULL" THEN 0
      ELSE StakeOf({ v \in Nodes : votes[slot][v] = "Final" })
    fastCond == notarStake >= THRESH80
    notarCond == notarStake >= THRESH60
    finalCond == finalStake >= THRESH60
    fastCert == << "FastFinal", slot, block >>
    notarCert == << "Notar", slot, block >>
    finalCert == << "Final", slot, block >>
  IN
    /\ IF fastCond /\ ~(fastCert \in certs) THEN
         certs' = certs \cup { fastCert }
       ELSE IF notarCond /\ ~(notarCert \in certs) THEN
         certs' = certs \cup { notarCert }
       ELSE IF finalCond /\ ~(finalCert \in certs) THEN
         certs' = certs \cup { finalCert }
       ELSE
         certs' = certs
    /\ UNCHANGED << votes, pendingBlock >>

(************************************************************************)
(* Node behaviors (abstract) *)
(************************************************************************)
CastNotar(slot, v) ==
  /\ pendingBlock[slot] # "NULL"
  /\ votes' = [ votes EXCEPT ![slot][v] = "Notar" ]
  /\ UNCHANGED << certs, pendingBlock >>

CastFinalIfSeenNotarCert(slot, v) ==
  /\ pendingBlock[slot] # "NULL"
  /\ << "Notar", slot, pendingBlock[slot] >> \in certs
  /\ votes' = [ votes EXCEPT ![slot][v] = "Final" ]
  /\ UNCHANGED << certs, pendingBlock >>

(************************************************************************)
(* Next relation *)
(************************************************************************)
Next ==
  \/ \E slot \in Slots, v \in Nodes : CastNotar(slot, v)
  \/ \E slot \in Slots, v \in Nodes : CastFinalIfSeenNotarCert(slot, v)
  \/ \E slot \in Slots : BuildCerts(slot)

Spec == Init /\ [][Next]_<<votes, certs, pendingBlock>>

=============================================================================
\* Modification History
\* Last modified Sun Sep 28 12:47:22 IST 2025 by Shanmukha
\* Created Sun Sep 28 12:19:47 IST 2025 by Shanmukha
