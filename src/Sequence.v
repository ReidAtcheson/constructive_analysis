Require Import Coq.QArith.QArith_base.


Definition abs (r:Q) := if (Qlt_le_dec r 0) then -r else r.

Record convergent_sequence := {
  (*Sequence is function from nats to rationals*)
  seq : positive -> Q;
  (*r is number it converges to*)
  r : Q;
  (*a is modulus of convergence*)
  a : positive -> positive;
  (*Specification of modulus*)
  a_spec : forall n, abs ((seq (a n)) + -r) <= 1#n;
}.


Definition seq_ex1 (n : positive) := 1#n.
Definition r_ex1 := 0.
Definition a_ex1 (n : positive) := n.

Lemma z_eq_minus_z : 0 == -0.


Lemma a_spec_ex1 : forall n, abs ((seq_ex1 (a_ex1 n)) + -r_ex1) <= 1#n.
Proof.
intros.
unfold abs, seq_ex1,a_ex1,r_ex1.
destruct (Qlt_le_dec ((1 # n) + - 0) 0).
SearchAbout( 0 == -0).
* apply Qplus_0_r in q.
*

Qed.




