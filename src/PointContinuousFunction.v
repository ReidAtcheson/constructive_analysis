Require Import Coq.QArith.QArith_base.
Require Import Psatz.
Require Import Sequence.

Definition abs (r:Q) := if (Qlt_le_dec r 0) then -r else r.

Record point_continuous_function := {
  f : Q -> Q;
  r : Q;
  f_spec : forall s : convergent_sequence, (Sequence.r s)==r 
      ->  exists q : convergent_sequence,  ((Sequence.seq q)= fun n => (f (Sequence.seq s n))) /\ ((Sequence.r q) == (f r));
}.