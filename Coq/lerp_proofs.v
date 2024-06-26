Require Import Coq.Reals.Reals.

Open Scope R_scope.

Lemma lerpHomog0_LAW_DEF_2 :
  (* Assumptions *)
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 : R,
      lerp x0 x1 0 = x0
  ) ->
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0
  ) ->
  
  (* Arguments *)
  forall lerp lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 t : R,
  
  (* Conjecture *)
    lerpHomog0 x0 x1 t = lerp x0 x1 t - x0.
Proof.
  intro H_lerp_zero.
  intro H_lerpHomog0_def_1.

  intro lerp.
  intro lerpHomog0.
  intros x0 x1 t.

  rewrite (H_lerpHomog0_def_1 lerp).
  rewrite (H_lerp_zero lerp).
  reflexivity.
Qed.


Lemma lerpHomog0_LAW_ZERO_AXIOMS1 :
  (* Assumptions *)
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 : R,
      lerp x0 x1 0 = x0
  ) ->
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 0 = 0.
Proof.
  intro H_lerp_zero.
  intro H_lerpHomog0_def_1.

  intro lerpHomog0.
  assert (lerp : R -> R -> R -> R) by assumption.
  intros x0 x1.

  rewrite (H_lerpHomog0_def_1 lerp).
  rewrite (H_lerp_zero lerp).
  ring.
Qed.


Lemma lerpHomog0_LAW_ZERO_AXIOMS2 :
  (* Assumptions *)
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - x0
  ) ->
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 : R,
      lerp x0 x1 0 = x0
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 0 = 0.
Proof.
  intro H_lerpHomog0_def_2.
  intro H_lerp_zero.

  intro lerpHomog0.
  assert (lerp : R -> R -> R -> R) by assumption.
  intros x0 x1.

  rewrite (H_lerpHomog0_def_2 lerp).
  rewrite (H_lerp_zero lerp).
  ring.
Qed.


Lemma lerpHomog0_LAW_DEF_5 :
  (* Assumptions *)
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 : R,
      lerp x0 x1 1 = x1
  ) ->
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - x0
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 1 = x1 - x0.
Proof.
  intro H_lerp_unit.
  intro H_lerpHomog0_def_2.

  intro lerpHomog0.
  assert (lerp : R -> R -> R -> R) by assumption.
  intros x0 x1.

  rewrite (H_lerpHomog0_def_2 lerp).
    (* I think something has gone wrong with my names here... *)
  rewrite (H_lerp_unit lerp).
  reflexivity.
Qed.


Lemma lerpHomog0_LAW_DEF_6_AXIOMS1 :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 a t0 b t1 : R,
      lerpHomog0 x0 x1 (a*t0 + b*t1) = a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1
  ) ->
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 : R,
      lerpHomog0 x0 x1 1 = x1 - x0
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 c : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1.
Proof.
  intro H_lerpHomog0_linear.
  intro H_lerpHomog0_def_5.

  intro lerpHomog0.
  intros x0 x1 c.

  assert (H: c = c * 1 + 0 * 0) by ring.
  rewrite H at 1.
  assert (H1: c * lerpHomog0 x0 x1 1 = c*lerpHomog0 x0 x1 1 + 0*lerpHomog0 x0 x1 0).
  - rewrite H.
    ring.
  - rewrite H_lerpHomog0_linear with (a := c) (t0 := 1) (b := 0) (t1 := 0).
    ring.
Qed.


Lemma lerpHomog0_LAW_DEF_6_AXIOMS2 :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 c : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1.
Proof.
  intro H_lerpHomog0_impl.

  intro lerpHomog0.
  intros x0 x1 c.

  rewrite (H_lerpHomog0_impl lerpHomog0).
  rewrite (H_lerpHomog0_impl lerpHomog0).
  ring.
Qed.


Lemma lerpHomog0_LAW_IMPL :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R, lerpHomog0 x0 x1 c = c * lerpHomog0 x0 x1 1
  ) ->
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 : R, lerpHomog0 x0 x1 1 = x1 - x0
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 c : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 c = c*(x1 - x0).
Proof.
  intro H_lerpHomog0_def_6.
  intro H_lerpHomog0_def_5.

  intro lerpHomog0.
  intros x0 x1 c.

  rewrite H_lerpHomog0_def_6.
  rewrite H_lerpHomog0_def_5.
  reflexivity.
Qed.


Lemma lerpHomog0_LAW_AFFINE :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->

  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x y0 y1 a b : R,

  (* Conjecture *)
    lerpHomog0 (a*y0+b) (a*y1+b) x = a*(lerpHomog0 y0 y1 x).
Proof.
  intro H_lerpHomog0_impl.

  intro lerpHomog0.
  intros x y0 y1 a b.

  rewrite (H_lerpHomog0_impl).
  rewrite (H_lerpHomog0_impl).
  ring.
Qed.


Lemma lerp_LAW_IMPL_AXIOMS1:
  (* Assumptions *)
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - x0
  ) ->
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->

  (* Arguments *)
  forall lerp : R -> R -> R -> R,
  forall x0 x1 t : R,

  (* Conjecture *)
    lerp x0 x1 t = (1 - t) * x0 + t * x1.
Proof.
  intro H_lerpHomog0_def_1.
  intro H_lerpHomog0_impl.

  intro lerp.
  assert (lerpHomog0 : R -> R -> R -> R) by assumption.
  intros x0 x1 t.

  assert (H: lerp x0 x1 t = lerpHomog0 x0 x1 t + x0).
  - rewrite (H_lerpHomog0_def_1 lerp lerpHomog0).
    ring.
  - rewrite H.
    rewrite (H_lerpHomog0_impl lerpHomog0).
    ring.
Qed.


Lemma lerp_LAW_IMPL_AXIOMS2:
  (* Assumptions *)
  ( forall lerp lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerpHomog0 x0 x1 t = lerp x0 x1 t - x0
  ) ->
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->

  (* Arguments *)
  forall lerp : R -> R -> R -> R,
  forall x0 x1 t : R,

  (* Conjecture *)
    lerp x0 x1 t = (1 - t) * x0 + t * x1.
Proof.
  intro H_lerpHomog0_def_2.
  intro H_lerpHomog0_impl.

  intro lerp.
  assert (lerpHomog0 : R -> R -> R -> R) by assumption.
  intros x0 x1 t.

  assert (H: lerp x0 x1 t = lerpHomog0 x0 x1 t + x0).
  - rewrite (H_lerpHomog0_def_2 lerp lerpHomog0).
    ring.
  - rewrite H.
    rewrite (H_lerpHomog0_impl lerpHomog0).
    ring.
Qed.


Lemma lerp_LAW_ZERO :
  (* Assumptions *)
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerp x0 x1 t = (1 - t) * x0 + t * x1
  ) ->

  (* Arguments *)
  forall lerp : R -> R -> R -> R,
  forall x0 x1 : R,

  (* Conjecture *)
    lerp x0 x1 0 = x0.
Proof.
  intro H_lerp_impl.

  intro lerp.
  intros x0 x1.

  specialize (H_lerp_impl lerp x0 x1 0).
  rewrite H_lerp_impl.
  ring.
Qed.


Lemma lerp_LAW_UNIT :
  (* Assumptions *)
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerp x0 x1 t = (1 - t) * x0 + t * x1
  ) ->

  (* Arguments *)
  forall lerp : R -> R -> R -> R,
  forall x0 x1 : R,

  (* Conjecture *)
    lerp x0 x1 1 = x1.
Proof.
  intro H_lerp_impl.

  intro lerp.
  intros x0 x1.

  specialize (H_lerp_impl lerp x0 x1 1).
  rewrite H_lerp_impl.
  ring.
Qed.


Lemma lerpHomog0_LAW_DEF_1 :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->
  ( forall lerp : R -> R -> R -> R,
    forall x0 x1 t : R,
      lerp x0 x1 t = (1 - t) * x0 + t * x1
  ) ->

  (* Arguments *)
  forall lerp lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 t : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0.
Proof.
  intro H_lerpHomog0_impl.
  intro H_lerp_impl.

  intro lerp.
  intro lerpHomog0.
  intros x0 x1 t.

  rewrite (H_lerpHomog0_impl lerpHomog0).
  rewrite (H_lerp_impl lerp).
  rewrite (H_lerp_impl lerp).
  ring.
Qed.


Lemma lerpHomog0_LAW_LINEAR :
  (* Assumptions *)
  ( forall lerpHomog0 : R -> R -> R -> R,
    forall x0 x1 c : R,
      lerpHomog0 x0 x1 c = c*(x1 - x0)
  ) ->
  
  (* Arguments *)
  forall lerpHomog0 : R -> R -> R -> R,
  forall x0 x1 a t0 b t1 : R,

  (* Conjecture *)
    lerpHomog0 x0 x1 (a*t0 + b*t1) = a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1.
Proof.
  intro H_lerpHomog0_impl.

  intro lerpHomog0.
  intros x0 x1 a t0 b t1.

  rewrite (H_lerpHomog0_impl lerpHomog0).
  rewrite (H_lerpHomog0_impl lerpHomog0).
  rewrite (H_lerpHomog0_impl lerpHomog0).
  ring.
Qed.
