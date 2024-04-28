Require Import Coq.Reals.Reals.

Open Scope R_scope.

Parameter lerp : R -> R -> R -> R.
Parameter lerpHomog0 : R -> R -> R -> R.

Axiom lerp_LAW_ZERO : forall x0 x1 : R, lerp x0 x1 0 = x0.
Axiom lerp_LAW_UNIT : forall x0 x1 : R, lerp x0 x1 1 = x1.
Axiom lerpHomog0_LAW_DEF_1 : forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0.
Axiom lerpHomog0_LAW_LINEAR : forall x0 x1 a t0 b t1 : R, lerpHomog0 x0 x1 (a*t0 + b*t1) = a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1.


Theorem lerpHomog0_LAW_DEF_2 : forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - x0.
Proof.
  intros.
  rewrite lerpHomog0_LAW_DEF_1.
  rewrite lerp_LAW_ZERO.
  reflexivity.
Qed.

Theorem lerpHomog0_LAW_ZERO : forall x0 x1 : R, lerpHomog0 x0 x1 0 = 0.
Proof.
  intros.
  rewrite lerpHomog0_LAW_DEF_2.
  rewrite lerp_LAW_ZERO.
  ring.
Qed.

Theorem lerpHomog0_LAW_DEF_5 : forall x0 x1 : R, lerpHomog0 x0 x1 1 = x1 - x0.
Proof.
  intros.
  rewrite lerpHomog0_LAW_DEF_2.
  rewrite lerp_LAW_UNIT.
  reflexivity.
Qed.

Theorem lerpHomog0_LAW_DEF_6 : forall x0 x1 c : R, lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1.
Proof.
  intros x0 x1 c.
  assert (H: c = c * 1 + 0 * 0) by ring.
  rewrite H at 1.
  assert (H1: c * lerpHomog0 x0 x1 1 = c*lerpHomog0 x0 x1 1 + 0*lerpHomog0 x0 x1 0) by ring.
  rewrite H1.
  rewrite <- lerpHomog0_LAW_LINEAR with (x0 := x0) (x1 := x1) (a := c) (t0 := 1) (b := 0) (t1 := 0).
  ring.
Qed.

Theorem lerpHomog0_LAW_IMPLEMENTATION : forall x0 x1 c : R, lerpHomog0 x0 x1 c = c*(x1 - x0).
Proof.
  intros.
  rewrite lerpHomog0_LAW_DEF_6.
  rewrite lerpHomog0_LAW_DEF_5.
  reflexivity.
Qed.

Theorem lerpHomog0_LAW_AFFINE : forall x y0 y1 a b : R, (lerpHomog0 (a*y0+b) (a*y1+b)) x = a*((lerpHomog0 y0 y1) x).
Proof.
  intros.
  rewrite lerpHomog0_LAW_IMPLEMENTATION.
  rewrite lerpHomog0_LAW_IMPLEMENTATION.
  ring.
Qed.


Theorem lerp_LAW_IMPLEMENTATION : forall x0 x1 t : R, lerp x0 x1 t = (1 - t) * x0 + t * x1.
Proof.
  intros x0 x1 t.
  assert (lerp x0 x1 t = lerpHomog0 x0 x1 t + x0).
  - rewrite lerpHomog0_LAW_DEF_2.
    ring.
  - rewrite H.
    rewrite lerpHomog0_LAW_IMPLEMENTATION.
    ring.
Qed.
