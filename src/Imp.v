Require Import ZArith.

Definition loc : Type := nat.

Inductive aexp: Type :=
| AInt (n: Z)
| AVar (x: loc)
| APlus (a0 a1: aexp)
| AMinus (a0 a1: aexp)
| AMult (a0 a1: aexp)
.

Inductive bexp: Type :=
| BTrue
| BFalse
| BEq (a0 a1: aexp)
| BLe (a0 a1: aexp)
| BNot (b: bexp)
| BAnd (b0 b1: bexp)
| BOr (b0 b1: bexp)
.

Inductive com: Type :=
| CSkip
| CAssign (x: loc) (a: aexp)
| CSeq (c0 c1: com)
| CIf (b: bexp) (c0 c1: com)
| CWhile (b: bexp) (c: com)
.