Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Sequence.
Require Import Utility.



Definition seq_ex1 q := 1/q.
Definition r_ex1 := 0.
Definition a_ex1 (q:Q) := q.



Lemma a_spec_ex1 : forall q, q>0 -> Qabs ((seq_ex1 (a_ex1 q)) + -r_ex1) <= 1/q.
Proof.
intros.
unfold seq_ex1.
unfold a_ex1.
unfold r_ex1.
rewrite z_eq_minus_z.
rewrite Qplus_0_r.
assert (H0 := q_pos_invq_pos q H).
assert (0<=1/q) by lra.
assert (H2 := Qabs_pos (1/q) (H1)).
rewrite H2.
apply Qle_refl.

Qed.


Lemma ex1' : ConvergentSequence seq_ex1 r_ex1 a_ex1.
Proof.
unfold ConvergentSequence.
intros.
apply a_spec_ex1.
exact H.
Qed.





