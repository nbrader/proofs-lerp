Require Import Coq.Reals.Reals.

Open Scope R_scope.

Parameter lerp : R -> R -> R -> R.
Parameter lerpHomog0 : R -> R -> R -> R.

Theorem lerpHomog0_LAW_DEF_2 :
  (* Declarations *)
  forall (lerp : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerp_zero *)      (forall x0 x1 : R, lerp x0 x1 0 = x0) ->
  (* H_lerpHomog0_def *) (forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0) ->

  (* Arguments *)
  forall x0 x1 t : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 t = lerp x0 x1 t - x0.
Proof.
  (* Declarations *)
  intro lerp.

  (* Assumptions *)
  intro H_lerp_zero.
  intro H_lerpHomog0_def.

  (* Arguments *)
  intros x0 x1 t.

  (* Proof *)
  rewrite H_lerpHomog0_def.
  rewrite H_lerp_zero.
  reflexivity.
Qed.


Theorem lerpHomog0_LAW_ZERO :
  (* Declarations *)
  forall (lerp : R -> R -> R -> R),
  
  (* Assumptions *)
  (* H_lerp_zero *)      (forall x0 x1 : R, lerp x0 x1 0 = x0) ->
  (* H_lerpHomog0_def *) (forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0) ->

  (* Arguments *)
  forall (x0 x1 : R),

  (* Conjecture *)
    lerpHomog0 x0 x1 0 = 0.

Proof.
  (* Declarations *)
  intro lerp.

  (* Assumptions *)
  intro H_lerp_zero.
  intro H_lerpHomog0_def.

  (* Arguments *)
  intros x0 x1.
  
  (* Proof *)
  rewrite H_lerpHomog0_def.
  rewrite H_lerp_zero.
  ring.
Qed.


Theorem lerpHomog0_LAW_DEF_5 :
  (* Declarations *)
  forall (lerp : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerp_unit *)      (forall x0 x1 : R, lerp x0 x1 1 = x1) ->
  (* H_lerpHomog0_def_2 *)(forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - x0) ->

  (* Arguments *)
  forall x0 x1 : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 1 = x1 - x0.
Proof.
  (* Declarations *)
  intro lerp.

  (* Assumptions *)
  intro H_lerp_unit.
  intro H_lerpHomog0_def_2.

  (* Arguments *)
  intros x0 x1.

  (* Proof *)
  rewrite H_lerpHomog0_def_2.
  rewrite H_lerp_unit.
  reflexivity.
Qed.


Theorem lerpHomog0_LAW_DEF_6 :
  (* Declarations *)
  forall (lerpHomog0 : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerpHomog0_linear *) (forall x0 x1 a t0 b t1 : R, lerpHomog0 x0 x1 (a*t0 + b*t1) = a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1) ->
  (* H_lerpHomog0_def_5 *) (forall x0 x1 : R, lerpHomog0 x0 x1 1 = x1 - x0) ->

  (* Arguments *)
  forall x0 x1 c : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1.
Proof.
  (* Declarations *)
  intro lerpHomog0.

  (* Assumptions *)
  intro H_lerpHomog0_linear.
  intro H_lerpHomog0_def_5.

  (* Arguments *)
  intros x0 x1 c.

  (* Proof *)
  assert (H: c = c * 1 + 0 * 0) by ring.
  rewrite H at 1.
  assert (H1: c * lerpHomog0 x0 x1 1 = c*lerpHomog0 x0 x1 1 + 0*lerpHomog0 x0 x1 0).
  - rewrite H.
    ring.
  - rewrite H_lerpHomog0_linear with (a := c) (t0 := 1) (b := 0) (t1 := 0).
    ring.
Qed.


Theorem lerpHomog0_LAW_IMPLEMENTATION :
  (* Declarations *)
  forall (lerpHomog0 : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerpHomog0_def_6 *) (forall x0 x1 c : R, lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1) ->
  (* H_lerpHomog0_def_5 *) (forall x0 x1 : R, lerpHomog0 x0 x1 1 = x1 - x0) ->

  (* Arguments *)
  forall x0 x1 c : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 c = c*(x1 - x0).
Proof.
  (* Declarations *)
  intro lerpHomog0.

  (* Assumptions *)
  intro H_lerpHomog0_def_6.
  intro H_lerpHomog0_def_5.

  (* Arguments *)
  intros x0 x1 c.

  (* Proof *)
  rewrite H_lerpHomog0_def_6.
  rewrite H_lerpHomog0_def_5.
  reflexivity.
Qed.


Theorem lerpHomog0_LAW_AFFINE :
  (* Declarations *)
  forall (lerpHomog0 : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerpHomog0_impl *) (forall x0 x1 c : R, lerpHomog0 x0 x1 c = c*(x1 - x0)) ->

  (* Arguments *)
  forall x y0 y1 a b : R,

  (* Conjecture *)
    lerpHomog0 (a*y0+b) (a*y1+b) x = a*(lerpHomog0 y0 y1 x).
Proof.
  (* Declarations *)
  intro lerpHomog0.

  (* Assumptions *)
  intro H_lerpHomog0_impl.

  (* Arguments *)
  intros x y0 y1 a b.

  (* Proof *)
  rewrite H_lerpHomog0_impl by assumption.
  rewrite H_lerpHomog0_impl by assumption.
  ring.
Qed.


Theorem lerp_LAW_IMPLEMENTATION :
  (* Declarations *)
  forall (lerp : R -> R -> R -> R) (lerpHomog0 : R -> R -> R -> R),

  (* Assumptions *)
  (* H_lerpHomog0_def *) (forall x0 x1 t : R, lerpHomog0 x0 x1 t = lerp x0 x1 t - x0) ->
  (* H_lerpHomog0_impl *) (forall x0 x1 c : R, lerpHomog0 x0 x1 c = c*(x1 - x0)) ->

  (* Arguments *)
  forall x0 x1 t : R,

  (* Conjecture *)
    lerp x0 x1 t = (1 - t) * x0 + t * x1.
Proof.
  (* Declarations *)
  intro lerp.
  intro lerpHomog0.

  (* Assumptions *)
  intro H_lerpHomog0_def.
  intro H_lerpHomog0_impl.

  (* Arguments *)
  intros x0 x1 t.

  (* Proof *)
  assert (H: lerp x0 x1 t = lerpHomog0 x0 x1 t + x0).
  - rewrite H_lerpHomog0_def.
    ring.
  - rewrite H.
    rewrite H_lerpHomog0_impl.
    ring.
Qed.
