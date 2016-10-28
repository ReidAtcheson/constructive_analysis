Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Sequence.
Require Import PointContinuousFunction.

Definition IncreasingFunction_def f := forall x y , x<y -> (f x) <= (f y).

Definition ContinuousFunction_def f w :=
  PointContinuousFunction_def w 0 /\
  IncreasingFunction_def w /\
  forall q, q==0 -> w q == 0 /\
  forall x y, Qabs ((f x) + -(f y)) <=
              w (Qabs (x + -y)).
                           


Record ContinuousFunction :=
  {
    Continf : Q -> Q;
    Continw : Q -> Q;
    Contin_spec : ContinuousFunction_def Continf Continw;
  }.








