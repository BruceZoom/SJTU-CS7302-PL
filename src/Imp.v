Require Import Coq.ZArith.ZArith.


Definition loc : Type := nat.

Inductive aexp: Type :=
| AInt (n: Z)
| AVar (x: loc)
| APlus (a0 a1: aexp)
| AMinus (a0 a1: aexp)
| AMult (a0 a1: aexp)
.

Coercion AInt : Z >-> aexp.
Coercion AVar : loc >-> aexp.

Declare Scope aexp_scope.
Bind Scope aexp_scope with aexp.

Notation "a0 + a1" := (APlus a0 a1) : aexp_scope.
Notation "a0 - a1" := (AMinus a0 a1) : aexp_scope.
Notation "a0 * a1" := (AMult a0 a1) : aexp_scope.


Inductive bexp: Type :=
| BTrue
| BFalse
| BEq (a0 a1: aexp)
| BLe (a0 a1: aexp)
| BNot (b: bexp)
| BAnd (b0 b1: bexp)
| BOr (b0 b1: bexp)
.

Declare Scope bexp_scope.
Bind Scope bexp_scope with bexp.

Notation "'T'" := (BTrue) : bexp_scope.
Notation "'F'" := (BFalse) : bexp_scope.
Notation "a0 == a1" := (BEq a0 a1) (at level 80) : bexp_scope.
Notation "a0 <= a1" := (BLe a0 a1) : bexp_scope.
Notation "! b" := (BNot b) (at level 30) : bexp_scope.
Notation "b0 && b1" := (BAnd b0 b1) : bexp_scope.
Notation "b0 || b1" := (BOr b0 b1) : bexp_scope.

Notation "a0 != a1" := (BNot (BEq a0 a1)) (at level 80) : bexp_scope.

Inductive com: Type :=
| CSkip
| CAssign (x: loc) (a: aexp)
| CSeq (c0 c1: com)
| CIf (b: bexp) (c0 c1: com)
| CWhile (b: bexp) (c: com)
.

Declare Scope com_scope.
Bind Scope com_scope with com.

Notation "'Skip'" := (CSkip) : com_scope.
Notation "x ::= a" := (CAssign x a) (at level 199) : com_scope.
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 200) : com_scope.
Notation "'If' b 'Then' c1 'Else' c2" := (CIf b c1 c2) (at level 200) : com_scope.
Notation "'While' b 'Do' c" := (CWhile b c) (at level 200) : com_scope.


Open Scope aexp_scope.
Open Scope bexp_scope.
Open Scope com_scope.

Example Euclid (M N: loc) :=
  While M != N Do
    If M <= N
      Then N ::= N - M
      Else M ::= M - N
.
