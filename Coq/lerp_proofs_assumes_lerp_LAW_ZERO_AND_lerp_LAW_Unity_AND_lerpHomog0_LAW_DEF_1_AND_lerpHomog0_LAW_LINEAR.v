Require Import Coq.Reals.Reals.
Require Import LerpProofs.lerp_proofs.

Open Scope R_scope.

Axiom lerp_LAW_ZERO : forall lerp : R -> R -> R -> R, forall x0 x1 : R, lerp x0 x1 0 = x0.
Axiom lerp_LAW_UNIT : forall lerp : R -> R -> R -> R, forall x0 x1 : R, lerp x0 x1 1 = x1.
Axiom lerpHomog0_LAW_DEF_1 : forall lerp lerpHomog0 : R -> R -> R -> R, forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0.
Axiom lerpHomog0_LAW_LINEAR : forall lerpHomog0 : R -> R -> R -> R, forall x0 x1 a t0 b t1 : R, lerpHomog0 x0 x1 (a*t0 + b*t1) = a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1.

Definition lerpHomog0_LAW_DEF_2 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_2 lerp_LAW_ZERO lerpHomog0_LAW_DEF_1.
Definition lerpHomog0_LAW_ZERO := LerpProofs.lerp_proofs.lerpHomog0_LAW_ZERO_AXIOMS1 lerp_LAW_ZERO lerpHomog0_LAW_DEF_1.
Definition lerpHomog0_LAW_DEF_5 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_5 lerp_LAW_UNIT lerpHomog0_LAW_DEF_2.
Definition lerpHomog0_LAW_DEF_6 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_6_AXIOMS1 lerpHomog0_LAW_LINEAR lerpHomog0_LAW_DEF_5.
Definition lerpHomog0_LAW_IMPL := LerpProofs.lerp_proofs.lerpHomog0_LAW_IMPL lerpHomog0_LAW_DEF_6 lerpHomog0_LAW_DEF_5.
Definition lerpHomog0_LAW_AFFINE := LerpProofs.lerp_proofs.lerpHomog0_LAW_AFFINE lerpHomog0_LAW_IMPL.
Definition lerp_LAW_IMPL := LerpProofs.lerp_proofs.lerp_LAW_IMPL_AXIOMS1 lerpHomog0_LAW_DEF_2 lerpHomog0_LAW_IMPL.