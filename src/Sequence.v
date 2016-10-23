Require Import Coq.QArith.QArith_base.
Require Import Psatz.


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

Lemma z_eq_minus_z : -0 == 0.
Proof.
lra.
Qed.


Lemma a_spec_ex1 : forall n, abs ((seq_ex1 (a_ex1 n)) + -r_ex1) <= 1#n.
Proof.
intros.
unfold abs, seq_ex1,a_ex1,r_ex1.
destruct (Qlt_le_dec ((1 # n) + - 0) 0).
* assert ((1#n) < 0) by lra.
  assert (R: (1 # n) + - 0 == 1 # n) by lra.
  rewrite R.
  assert (~ 1 # n < 0). {
    apply Qle_not_lt.
    auto with *.
  }
  contradiction.
* rewrite z_eq_minus_z.
  lra.
Qed.


Definition ex1 : convergent_sequence.
Proof.
apply Build_convergent_sequence with (seq:=seq_ex1) (r:=r_ex1) (a:=a_ex1).
apply a_spec_ex1.
Qed.




