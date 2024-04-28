Require Import Coq.Reals.Reals.
Require Import LerpProofs.lerp_proofs.

Open Scope R_scope.

Axiom lerp_LAW_IMPL : forall lerp : R -> R -> R -> R, forall x0 x1 t : R, lerp x0 x1 t = (1 - t) * x0 + t * x1.
Axiom lerpHomog0_LAW_IMPL : forall lerpHomog0 : R -> R -> R -> R, forall x0 x1 c : R, lerpHomog0 x0 x1 c = c*(x1 - x0).

Definition lerp_LAW_ZERO := LerpProofs.lerp_proofs.lerp_LAW_ZERO lerp_LAW_IMPL.
Definition lerp_LAW_UNIT := LerpProofs.lerp_proofs.lerp_LAW_UNIT lerp_LAW_IMPL.
Definition lerpHomog0_LAW_DEF_1 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_1 lerpHomog0_LAW_IMPL lerp_LAW_IMPL.
Definition lerpHomog0_LAW_DEF_2 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_2 lerp_LAW_ZERO lerpHomog0_LAW_DEF_1.
Definition lerpHomog0_LAW_ZERO := LerpProofs.lerp_proofs.lerpHomog0_LAW_ZERO_AXIOMS1 lerp_LAW_ZERO lerpHomog0_LAW_DEF_1.
Definition lerpHomog0_LAW_LINEAR := LerpProofs.lerp_proofs.lerpHomog0_LAW_LINEAR lerpHomog0_LAW_IMPL.
Definition lerpHomog0_LAW_AFFINE := LerpProofs.lerp_proofs.lerpHomog0_LAW_AFFINE lerpHomog0_LAW_IMPL.
Definition lerpHomog0_LAW_DEF_5 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_5 lerp_LAW_UNIT lerpHomog0_LAW_DEF_2.
Definition lerpHomog0_LAW_DEF_6 := LerpProofs.lerp_proofs.lerpHomog0_LAW_DEF_6_AXIOMS1 lerpHomog0_LAW_LINEAR lerpHomog0_LAW_DEF_5.
