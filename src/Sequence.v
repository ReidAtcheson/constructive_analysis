Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Psatz.


Definition ConvergentSequence 
(seq : Q->Q)
(r:Q)
(a:Q->Q) 
:= (forall q, q>0 -> Qabs ((seq (a q)) + -r) <= 1/q).


(*
Definition pos2Q (p : positive)
:= let zp := Zpos p in
zp#1.

Definition Q2pos (q : Q)
:= Z.to_pos (Qfloor q).

Lemma pos_of_pos_is_pos : 
forall (n : Z), 
(Z.lt 0 n) -> Zpos (Z.to_pos n) = n.
Proof.
apply Z2Pos.id.
Qed.


Lemma ints_preserve : forall (n:Z), 
Z.gt n 0 -> (pos2Q (Q2pos (n#1)))==n#1.
Proof.
intros.
unfold pos2Q.
unfold Q2pos.
unfold Qfloor.
assert( (Z.div n (Zpos xH) = n) ).
{
  auto with *.
}
rewrite H0.
rewrite Z2Pos.id.
auto with *.
auto with *.
Qed.
*)
