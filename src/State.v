Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import PL.Imp.

Definition state : Type := loc -> Z.

Definition update (st: state) (x: loc) (v: Z) : state :=
  fun y => if eqb x y then v else st y.

