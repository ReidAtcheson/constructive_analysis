Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Coq.QArith.Qround.
Require Import Coq.PArith.Pnat.
Require Import Sequence.
Require Import Utility.


Definition a := 5#1.
Definition b := 2#1.
Definition seq_ex1 q:= a+b/q.
Definition r_ex1 := a.



Definition a_ex1 q := q*b.






Lemma a_spec_ex1 : forall q, q>0 -> Qabs ((seq_ex1 (a_ex1 q)) + -r_ex1) <= 1/q.
Proof.
intros.
unfold seq_ex1.
unfold a_ex1.
unfold r_ex1.
assert( a + b / (q * b) + - a == b / (q * b)) by lra.
rewrite H0.
assert( b / (q*b)==b * (/q) * (/b) ).
{
  assert(b * (/q) * (/b) == b * ((/q) * (/b))) by lra.
  assert( H2 := Qinv_mult_distr q b).
  assert(/q * /b == /(q*b)) by lra.
  rewrite H3 in H1.
  auto with *.
}
rewrite H1.
assert ( b * / q * / b == /q ).
{
  assert( b * / q * / b == (b * /b) * /q) by lra.
  rewrite H2.
  assert( b * /b == 1) by auto with *.
  rewrite H3.
  lra.
}
rewrite H2.
assert( H3 := qinvq_eq_1divq q).
rewrite H3.

assert( H4 := q_pos_invq_pos q H ).
assert( 0 <= 1/q ) by lra.
assert( H6 := Qabs_pos (1/q) H5 ).
rewrite H6.
apply Qle_refl.

Qed.


Lemma ex1' : ConvergentSequence_def seq_ex1 r_ex1 a_ex1.
Proof.
unfold ConvergentSequence_def.
intros.
apply (a_spec_ex1 q).
auto.
Qed.



Lemma ex1p : ConvergentSequence.
Proof.
  apply Build_ConvergentSequence with (Seq := seq_ex1) (Seqr := r_ex1) (Seqa := a_ex1).
  apply ex1'.
Qed.



