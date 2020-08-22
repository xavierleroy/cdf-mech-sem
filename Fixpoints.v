(** Computing least fixed points, following the Knaster-Tarski theorem. *)

From Coq Require Import Extraction ExtrOcamlBasic.

Section KNASTER_TARSKI.

(** Consider a type [A] equipped with a decidable equality [eq] and a
    transitive ordering [le]. *)

Variable A: Type.

Variable eq: A -> A -> Prop.
Variable eq_dec: forall (x y: A), {eq x y} + {~eq x y}.

Variable le: A -> A -> Prop.
Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.
Hypothesis eq_le: forall x y, eq x y -> le y x.

(** This is the strict order induced by [le].  We assume it is well-founded:
    all strictly ascending chains are finite. *)

Definition gt (x y: A) := le y x /\ ~eq y x.

Hypothesis gt_wf: well_founded gt.

(** Let [bot] be a smallest element of [A]. *)

Variable bot: A.
Hypothesis bot_smallest: forall x, le bot x.

Section FIXPOINT.

(** Let [F] be a monotonically increasing function from [A] to [A]. *)

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).

Lemma iterate_acc:
  forall (x: A) (acc: Acc gt x) (PRE: le x (F x)) (NEQ: ~eq x (F x)), Acc gt (F x).
Proof.
  intros. apply Acc_inv with x; auto. split; auto.
Defined.

Lemma iterate_le:
  forall (x: A) (PRE: le x (F x)), le (F x) (F (F x)).
Proof.
  intros. apply F_mon. apply PRE.
Qed.

(** We iterate [F] starting from a pre-fixed-point [x], that is, an [x]
    such that [le x (F x)].  This is a structural recursion over a derivation
    of accessibility [Acc gt x] of [x], that is, over the proof that
    all strictly increasing sequences starting from [x] are finite.
    This guarantees that the iteration always terminates! *)

Fixpoint iterate (x: A) (acc: Acc gt x) (PRE: le x (F x)) {struct acc}: A :=
  let x' := F x in
  match eq_dec x x' with
  | left E => x
  | right NE => iterate x' (iterate_acc x acc PRE NE) (iterate_le x PRE)
  end.

(** The fixed point is obtained by iterating from [bot]. *)

Definition fixpoint : A := iterate bot (gt_wf bot) (bot_smallest (F bot)).

(** It is solution to the fixed point equation. *)

Lemma fixpoint_eq: eq fixpoint (F fixpoint).
Proof.
  assert (REC: forall x acc PRE, eq (iterate x acc PRE) (F (iterate x acc PRE))).
  { induction x using (well_founded_induction gt_wf). intros. destruct acc; cbn.
    destruct (eq_dec x (F x)).
    - auto.
    - apply H. split; auto.
  }
  apply REC.
Qed.

(** It is the smallest post-fixed point. *)

Lemma fixpoint_smallest: forall z, le (F z) z -> le fixpoint z.
Proof.
  intros z LEz.
  assert (REC: forall x acc PRE, le x z -> le (iterate x acc PRE) z).
  { induction x using (well_founded_induction gt_wf). intros. destruct acc; cbn.
    destruct (eq_dec x (F x)).
    - auto.
    - apply H. split; auto.
      apply le_trans with (F z). apply F_mon; auto. apply LEz.
  }
  apply REC. apply bot_smallest.
Qed.

End FIXPOINT.

(** If a function [F] is pointwise below another function [G],
    the fixed point of [F] is below that of [G]. *)

Section FIXPOINT_MON.

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).
Variable G: A -> A.
Hypothesis G_mon: forall x y, le x y -> le (G x) (G y).
Hypothesis F_le_G: forall x, le (F x) (G x).

Theorem fixpoint_mon: le (fixpoint F F_mon) (fixpoint G G_mon).
Proof.
  apply fixpoint_smallest. 
  eapply le_trans. apply F_le_G. apply eq_le. apply fixpoint_eq.
Qed.

End FIXPOINT_MON.

End KNASTER_TARSKI.

(** Let's ask Coq to extract OCaml executable code from the definition of
    [fixpoint], we see that the arguments [acc] and[PRE] disappear,
    because their only purpose is to prove termination.
    The extracted OCaml code is exactly the code we would have written
    by hand! *)

Recursive Extraction fixpoint.

(** Result:
<<
(** val iterate : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iterate eq_dec f x =
  let x' = f x in if eq_dec x x' then x else iterate eq_dec f x'

(** val fixpoint : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 -> 'a1) -> 'a1 **)

let fixpoint eq_dec bot f =
  iterate eq_dec f bot
>>
*)
