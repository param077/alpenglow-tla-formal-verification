----------------------------- MODULE RotorSlice -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Constants to set when running TLC:
    NODES     -- a finite set of node ids (e.g. {"n1","n2","n3","n4"})
    HONEST    -- subset of NODES considered honest (the rest may be adversary)
    STAKE     -- function from NODES -> 0..1 giving relative stake (rationals)
                (TLC cannot do reals well; for TLC runs use integer-weighted stakes)
    LEADER    -- the leader node (must be in NODES)
    GAMMA     -- total number of shreds Γ (positive integer)
    GAMMA_REQ -- required number of shreds to decode γ (positive integer, <= GAMMA)

  Notes:
   - This spec models a single *slice* dissemination. To model a full block,
     run multiple slices independently or extend accordingly.
   - Erasure/encode is abstracted: we treat each shred as a tuple (idx, root).
***************************************************************************)

CONSTANTS NODES, HONEST, STAKE, LEADER, GAMMA, GAMMA_REQ

(***************************************************************************)
(* Types / Value abbreviations *)
Shred == [idx: 1..GAMMA, root: STRING]    \* root is abstract (Merkle root)
RelayAssign == [i \in 1..GAMMA |-> CHOOSE n \in NODES: TRUE]
    \* RelayAssign maps shred index -> node assigned to relay that shred.
    \* In Init it's nondeterministically chosen but must satisfy PS_P sample predicate.
(***************************************************************************)

VARIABLES
  Relay,         \* relay assignment function: 1..GAMMA -> NODES
  SentByLeader,  \* set of shred indices leader has sent (subset of 1..GAMMA)
  SentByRelay,   \* set of pairs <<relay, idx>> that relays have broadcast
  Received,      \* mapping node -> set of shreds (each shred = [idx, root])
  Decoded        \* set of nodes that have successfully decoded this slice

(***************************************************************************)
(* Helper: set of honest nodes, rotor success condition per Def.6:
   Rotor successful iff leader is honest and at least γ of the corresponding
   relays are honest. (We model "corresponding relays" = {Relay[i] : i in 1..Γ}.)
***************************************************************************)
RelaySet(rel) == { rel[i] : i \in 1..GAMMA }
NumHonestRelays(rel) == Cardinality(RelaySet(rel) \cap HONEST)
RotorSuccessCondition(rel) == (LEADER \in HONEST) /\ (NumHonestRelays(rel) >= GAMMA_REQ)

(***************************************************************************)
(* Abstract PS-P sampling predicate: must hold of Relay assignment.
   For TLC runs you can replace this with a concrete check (small instances).
   The whitepaper defines PS-P as:
     1) heavy nodes get floor(ρ_i * Γ) filled bins,
     2) partition the remaining fractional stakes into remaining bins,
     3) pick one node per bin proportional to stake.
   Here we only require that Relay is a function 1..GAMMA -> NODES and
   that heavy nodes receive at least floor(STAKE[n]*GAMMA) assignments.
***************************************************************************)
IsPSP(rel) ==
  /\ rel \in [1..GAMMA -> NODES]
  /\ \A n \in NODES :
       LET occ == Cardinality({ i \in 1..GAMMA : rel[i] = n })
           required == STAKE[n] * GAMMA
       IN occ >= required




(***************************************************************************)
(* Shred root modeling:
   We assume the leader defines a single correct Merkle root for this slice,
   called LEADER_ROOT. Adversarial leader could set different roots at relays;
   we model that by allowing a malicious leader to set arbitrary root values
   on sent shreds. For simplicity we let leader send the canonical root "R"
   when LEADER is honest; otherwise root can be "RA" (adversarial).
***************************************************************************)
LEADER_ROOT == "R"
ADV_ROOT    == "RA"

(***************************************************************************)
(* Init *)
Init ==
  LET r == CHOOSE x \in [1..GAMMA -> NODES] : IsPSP(x)
  IN /\ Relay = r
     /\ SentByLeader = {}
     /\ SentByRelay = {}
     /\ Received = [n \in NODES |-> {}]
     /\ Decoded = {}


(***************************************************************************)
(* Actions *)
(***************************************************************************)

(*
  LeaderSend(i): leader sends shred index i to assigned relay Relay[i].
  When leader is honest, the shred carries LEADER_ROOT; if leader is adversarial,
  the root may be arbitrary (modeled nondeterministically).
*)
LeaderSend(i) ==
  /\ i \in 1..GAMMA
  /\ i \notin SentByLeader
  /\ SentByLeader' = SentByLeader \cup {i}
  /\ UNCHANGED << Relay, SentByRelay, Received, Decoded >>
  /\ TRUE

(*
  RelayReceive(i): relay node r = Relay[i] receives a copy from leader
  (we model immediate reception; network delay and δ can be encoded by
  scheduling but omitted here for simplicity)
*)
RelayReceive(i) ==
  /\ i \in SentByLeader
  /\ << Relay[i], i >> \notin SentByRelay
  /\ LET r == Relay[i]
         root ==
           IF LEADER \in HONEST THEN LEADER_ROOT
           ELSE CHOOSE s \in {LEADER_ROOT, ADV_ROOT} : TRUE
     IN
       /\ SentByRelay' = SentByRelay \cup { << r, i >> }
       /\ Received' = [ n \in NODES |-> 
            IF n = r
              THEN Received[n] \cup { [ idx |-> i, root |-> root ] }
              ELSE Received[n]
          ]
       /\ UNCHANGED << Relay, SentByLeader, Decoded >>

(*
  RelayBroadcast(i,r): when relay r has its own shred (Received[r] contains idx i),
  it broadcasts to all other nodes (leader and itself excluded for optimization
  in paper, but here we broadcast to all to simplify).
*)
RelayBroadcast(i, r) ==
  /\ << r, i >> \in SentByRelay
  /\ LET sroot == CHOOSE sh \in Received[r] : sh.idx = i
     IN
       /\ \A n \in NODES :
            Received'[n] = Received[n] \cup { [ idx |-> i, root |-> sroot.root ] }
       /\ UNCHANGED << Relay, SentByLeader, SentByRelay, Decoded >>

(*
  NodeDecode(n): node n attempts to decode when it has >= GAMMA_REQ shreds
  that agree on the root value. We define CanDecode(n) accordingly.
*)
CanDecode(n) ==
  LET S == Received[n]
      roots == { r \in STRING : \E sh \in S : sh.root = r }
      GoodRoot(r) == Cardinality({ sh \in S : sh.root = r }) >= GAMMA_REQ
  IN \E r \in roots : GoodRoot(r)

NodeDecode(n) ==
  /\ n \in NODES
  /\ n \notin Decoded
  /\ CanDecode(n)
  /\ Decoded' = Decoded \cup { n }
  /\ UNCHANGED << Relay, SentByLeader, SentByRelay, Received >>

(***************************************************************************)
(* Next-state relation *)
Next ==
  \/ \E i \in 1..GAMMA : LeaderSend(i)
  \/ \E i \in 1..GAMMA : RelayReceive(i)
  \/ \E i \in 1..GAMMA, r \in NODES : RelayBroadcast(i, r)
  \/ \E n \in NODES : NodeDecode(n)

(***************************************************************************)
(* Specification *)
Spec == Init /\ [][Next]_<<Relay, SentByLeader, SentByRelay, Received, Decoded>>

(***************************************************************************)
(* Properties to check *)
\* Safety: A node never Decodes unless it has at least GAMMA_REQ matching shreds.
InvariantDecodeSound ==
  \A n \in NODES :
    n \in Decoded => CanDecode(n)

\* Liveness claim (temporal): If RotorSuccessCondition holds then eventually
\* every honest node will decode. This is a liveness property; TLC can check
\* on finite traces with fairness assumptions if you add a scheduler.
LivenessClaim ==
  []( RotorSuccessCondition(Relay) => <> \A n \in HONEST : n \in Decoded )

=============================================================================
\* Modification History
\* Last modified Sun Sep 28 15:57:12 IST 2025 by Shanmukha
\* Created Sun Sep 28 14:02:30 IST 2025 by Shanmukha
