From Coq Require Import Arith ZArith Psatz Bool String List.
From CDF Require Import Sequences IMP.

(** * 6.  Semantics of divergence, second part *)

(** ** 6.5.  The partiality monad *)

(** The type [delay A] represents computations that produce a result
    of type [A] if they terminate, but can also diverge. *)

CoInductive delay (A: Type) : Type :=
  | now: A -> delay A
  | later: delay A -> delay A.

Arguments now [A].
Arguments later [A].

(** The computation of type [A] that always diverges. *)

CoFixpoint omega (A: Type) : delay A := later (omega A).

(** A few technical definitions to prove equalities between computations. *)

Lemma u_delay:
  forall {A: Type} (x: delay A),
  x = match x with now v => now v | later y => later y end.
Proof. destruct x; auto. Qed.

Ltac unroll_delay X := rewrite (u_delay X); simpl.

Ltac samedelay :=
  match goal with
  [ |- ?X = ?Y ] => rewrite (u_delay X); simpl; auto
  end.

(** Terminating on a value [v] is captured by an inductive predicate
    [terminates x v].
    Diverging is captured by a coinductive predicate [diverges x]. *)

Inductive terminates {A: Type} : delay A -> A -> Prop :=
  | terminates_now:   forall v, terminates (now v) v
  | terminates_later: forall x v, terminates x v -> terminates (later x) v.

CoInductive diverges {A: Type} : delay A -> Prop :=
  | diverges_later: forall x, diverges x -> diverges (later x).

Lemma terminates_unique: forall (A: Type) (x: delay A) (v1 v2: A),
  terminates x v1 -> terminates x v2 -> v1 = v2.
Proof.
  intros until v2; intros T; revert x v1 T v2. induction 1; intros.
- inversion H; subst; auto.
- inversion H; subst; auto.
Qed.

Lemma terminates_diverges_excl: forall (A: Type) (x: delay A) (v: A),
  terminates x v -> diverges x -> False.
Proof.
  induction 1; intros D; inversion D; auto.
Qed.

(** Example of use: computing the remainder of Euclidean division. *)

CoFixpoint remainder (a b: nat) : delay nat :=
  if a <? b then now a else later (remainder (a - b) b).

Lemma remainder_terminates:
  forall a b, b > 0 -> 
  exists q r, terminates (remainder a b) r /\ r < b /\ a = b * q + r.
Proof.
  induction a using (well_founded_ind lt_wf). intros.
  unroll_delay (remainder a b). destruct (Nat.ltb_spec a b).
- exists 0, a. split. constructor. split. auto. lia. 
- assert (LT: a - b < a) by lia. 
  destruct (H _ LT b H0) as (q & r & P & Q & R).
  exists (S q), r. split. constructor; auto. split. auto. lia.
Qed.

Lemma remainder_diverges:
  forall a, diverges (remainder a 0).
Proof.
  cofix CIH; intros a. unroll_delay (remainder a 0). constructor. apply CIH.
Qed.

(** Equitermination of two computations. *)

Section EQUITERMINATION.

Context {A: Type}.

CoInductive equi: delay A -> delay A -> Prop :=
  | equi_terminates: forall x y v, terminates x v -> terminates y v -> equi x y
  | equi_later: forall x y, equi x y -> equi (later x) (later y).

Notation "x == y" := (equi x y) (at level 70, no associativity).

Lemma equi_refl: forall x, x == x.
Proof.
  cofix COINDHYP; intros; destruct x.
- apply equi_terminates with a; constructor.
- apply equi_later. apply COINDHYP.
Qed.

Lemma equi_refl': forall x y, x = y -> x == y.
Proof.
  intros; subst; apply equi_refl.
Qed.

Lemma equi_sym: forall x y, x == y -> y == x.
Proof.
  cofix COINDHYP; intros x y E; inversion E; subst.
- apply equi_terminates with v; auto.
- apply equi_later; apply COINDHYP; auto.
Qed.

Lemma terminates_equi: 
  forall x v, terminates x v -> forall y, x == y -> terminates y v.
Proof.
  induction 1; intros y E; inversion E; subst.
- inversion H; auto.
- inversion H0; subst. 
  assert (v0 = v) by (eapply terminates_unique; eauto). subst v0; auto.
- constructor; eauto.
Qed.

Lemma equi_trans: forall x y z, x == y -> y == z -> x == z.
Proof.
  cofix COINDHYP; intros x y z E1 E2; inversion E1; subst.
- apply equi_terminates with v. auto. apply terminates_equi with y; auto.
- inversion E2; subst.
+ inversion H0; subst. apply equi_terminates with v; auto. constructor. 
  apply terminates_equi with y0; auto using equi_sym.
+ constructor. apply COINDHYP with y0; auto.
Qed.

Lemma eq_later: forall x, later x == x.
Proof.
  cofix COINDHYP; intros x. destruct x. 
- apply equi_terminates with a; repeat constructor.
- apply equi_later. apply COINDHYP.
Qed. 

Lemma diverges_equi: forall x y, x == y -> diverges x -> diverges y.
Proof.
  cofix COINDHYP; intros. inversion H; subst.
- elim (terminates_diverges_excl A x v); auto.
- inversion H0; subst. constructor. eauto.
Qed. 

(** Weak bisimulation is another presentation of equitermination,
    with constructors [bisim_left] and [bisim_right] that enable us
    to "skip" a [later] constructor on one side but not on the other side.
    This simplifies many proofs.  However, we must prevent
    [bisim_left] or [bisim_right] to be applied infinitely often,
    because this would make [now v] and [bottom] bisimilar.  
    The extra argument of type [nat] limits the number of consecutive
    applications of the [bisim_left] and [bisim_right] rules.
    It is reset to an arbitrarily high value when [bisim_both] is applied. *)

CoInductive bisim: nat -> delay A -> delay A -> Prop :=
  | bisim_now: forall n v,
      bisim n (now v) (now v)
  | bisim_both: forall m n x y,
      bisim m x y -> bisim n (later x) (later y)
  | bisim_left: forall n x y,
      bisim n x y -> bisim (S n) (later x) y
  | bisim_right: forall n x y,
      bisim n x y -> bisim (S n) x (later y).

Lemma bisim_inv: forall n x y,
  bisim n x y ->
     (exists v, terminates x v /\ terminates y v)
  \/ (exists n' x' y', x = later x' /\ y = later y' /\ bisim n' x' y').
Proof.
  induction n using lt_wf_ind.
  intros x y B; inversion B; subst.
- left; exists v; split; constructor.
- right; exists m, x0, y0; auto.
- edestruct (H n0) as [(v & T1 & T2) | (n' & x' & y' & E1 & E2 & B')].
  lia. eauto.
  + left; exists v; auto using terminates_later.
  + right. exists (S n'), (later x'), y'; intuition auto.
    congruence. apply bisim_left; auto.
- edestruct (H n0) as [(v & T1 & T2) | (n' & x' & y' & E1 & E2 & B')].
  lia. eauto.
  + left; exists v; auto using terminates_later.
  + right. exists (S n'), x', (later y'); intuition auto.
    congruence. apply bisim_right; auto.
Qed.

Lemma bisim_equi: forall n x y,
  bisim n x y -> x == y.
Proof.
  cofix CIH; intros.
  destruct (bisim_inv _ _ _ H)
  as [(v & T1 & T2) | (n' & x' & y' & E1 & E2 & B')].
- apply equi_terminates with v; auto.
- subst. constructor. eauto.
Qed.

End EQUITERMINATION.

Notation "x == y" := (equi x y) (at level 70, no associativity).

(** The monad structure. *)

Definition ret := now.

CoFixpoint bind {A B: Type} (x: delay A) (f: A -> delay B) : delay B :=
  match x with
  | now v => later (f v)
  | later y => later (bind y f)
  end.

Remark bind_now: forall (A B: Type) (v: A) (f: A -> delay B),
  bind (now v) f = later (f v).
Proof. intros; samedelay. Qed.

Remark bind_later: forall (A B: Type) (x: delay A) (f: A -> delay B),
  bind (later x) f = later (bind x f).
Proof. intros; samedelay. Qed.

(** The three monadic laws hold up to equitermination. *)

Lemma mon_law_1: forall (A B: Type) (v: A) (f: A -> delay B),
  bind (now v) f == f v.
Proof. 
  intros. rewrite bind_now. apply eq_later.
Qed.

Lemma mon_law_2: forall (A: Type) (m: delay A), 
  bind m (@ret A) == m.
Proof.
  cofix CIH; intros. destruct m.
- rewrite bind_now. apply eq_later. 
- rewrite bind_later. constructor. apply CIH.
Qed.

Lemma mon_law_3: forall (A B C: Type) (m: delay A) (f: A -> delay B) (g: B -> delay C),
  bind (bind m f) g == bind m (fun x => bind (f x) g).
Proof.
  cofix CIH. intros; destruct m.
- rewrite ! bind_now, bind_later. apply equi_refl.
- rewrite ! bind_later. constructor. apply CIH.
Qed.

(** [bind] is compatible with equitermination [==]. *)

Lemma bind_terminates_l:
  forall (A: Type) (m: delay A) (v: A), terminates m v ->
  forall (B: Type) (f: A -> delay B), bind m f == f v.
Proof.
  induction 1; intros.
- apply mon_law_1.
- rewrite bind_later. eapply equi_trans. apply eq_later. apply IHterminates. 
Qed.

Lemma bind_context:
  forall (A B: Type) (m1 m2: delay A) (f1 f2: A -> delay B),
  m1 == m2 ->
  (forall v, f1 v == f2 v) ->
  bind m1 f1 == bind m2 f2.
Proof.
  cofix CIH; intros. inversion H; subst.
- apply equi_trans with (f1 v). apply bind_terminates_l; auto.
  apply equi_trans with (f2 v). auto.
  apply equi_sym. apply bind_terminates_l; auto.
- rewrite ! bind_later. constructor. apply CIH; auto.
Qed.

(** ** 6.6.  The monadic metalanguage *)

(** Here is the (coinductive) abstract syntax that expresses computations
    in the partiality monad. *)

CoInductive mon (A: Type): Type :=
  | Ret: A -> mon A
  | Later: mon A -> mon A
  | Bind: forall {B: Type}, mon B -> (B -> mon A) -> mon A.

Arguments Ret [A].
Arguments Later [A].
Arguments Bind [A B].

Lemma u_mon:
  forall {A: Type} (x: mon A),
  x = match x with Ret v => Ret v | Bind y f => Bind y f | Later m => Later m end.
Proof. destruct x; auto. Qed.

(** The semantics of an abstract syntax tree (of type [mon A])
    is defined by translation to the computation (of type [delay A])
    denoted by the syntax tree. *)

CoFixpoint run {A: Type} (m: mon A) : delay A :=
  match m with
  | Ret v => now v
  | Later m => later (run m)
  | Bind (Ret v) f => later (run (f v))
  | Bind (Later m) f => later (run (Bind m f))
  | Bind (Bind m f) g => later (run (Bind m (fun x => Bind (f x) g)))
  end.

Lemma run_Ret: forall (A: Type) (v: A), run (Ret v) = now v.
Proof. intros; samedelay. Qed.

Lemma run_Later: forall (A: Type) (m: mon A), run (Later m) = later (run m).
Proof. intros; samedelay. Qed.

Lemma run_Bind_Ret: forall (A B: Type) (v: A) (f: A -> mon B),
    run (Bind (Ret v) f) = later (run (f v)).
Proof. intros; samedelay. Qed.

Lemma run_Bind_Later: forall (A B: Type) (m: mon A) (f: A -> mon B),
    run (Bind (Later m) f) = later (run (Bind m f)).
Proof. intros; samedelay. Qed.

Lemma run_Bind_Bind: forall (A B C: Type) (m: mon A) (f: A -> mon B) (g: B -> mon C),
    run (Bind (Bind m f) g) = later (run (Bind m (fun x => Bind (f x) g))).
Proof. intros; samedelay. Qed.

(** Some of our proofs use continuations, which can also be viewed as
    contexts.  A context is a list of functions [A -> mon B] that
    can be composed using the "bind" operator. *)

Inductive cont: Type -> Type -> Type :=
  | K0: forall (A: Type), cont A A
  | Kbind: forall {A B C: Type} (f: A -> mon B) (k: cont B C), cont A C.

Fixpoint insert_cont {A B: Type} (k: cont A B): 
    forall {C: Type}, (B -> mon C) -> (A -> mon C) :=
  match k in cont A B 
  return forall {C: Type}, (B -> mon C) -> (A -> mon C) with
  | K0 A => fun C g => g
  | Kbind f k => fun D g a => Bind (f a) (insert_cont k g)
  end.

(** The three monadic laws.  *)

Lemma Mon_law_1: forall (A B: Type) (v: A) (f: A -> mon B),
  run (Bind (Ret v) f) == run (f v).
Proof. 
  intros. rewrite run_Bind_Ret; apply eq_later. 
Qed.

Lemma Mon_law_3: forall (A B C: Type) (m: mon A) (f: A -> mon B) (g: B -> mon C),
  run (Bind (Bind m f) g) == run (Bind m (fun x => Bind (f x) g)).
Proof.
  intros. rewrite run_Bind_Bind; apply eq_later.
Qed.

(** The second monadic law is difficult to prove.  We use a bisimulation
    approach based on the following relation. *)

Inductive eta_match: forall {A: Type}, nat -> mon A -> mon A -> Prop :=
| eta_match_1: forall {A: Type} (m: mon A),
    eta_match 1%nat (Bind m (@Ret _)) m
| eta_match_2: forall {A B C: Type} (m: mon A) (k: cont A B) (g: B -> mon C),
    eta_match 0%nat (Bind m (insert_cont k (fun x => Bind (g x) (@Ret _))))
                    (Bind m (insert_cont k g)).

Lemma Mon_law_2_aux:
  forall (A: Type) n (x y: mon A),
  eta_match n x y -> bisim n (run x) (run y).
Proof.
  cofix CIH; destruct 1.  
  - destruct m.
    + rewrite run_Bind_Ret, run_Ret.
      apply bisim_left. apply bisim_now.
    + rewrite run_Bind_Later, run_Later.
      eapply bisim_both. apply CIH. apply eta_match_1.
    + rewrite run_Bind_Bind.
      apply bisim_left. apply CIH.
      apply eta_match_2 with (k := K0 _).
  - destruct m.
    + rewrite ! run_Bind_Ret. destruct k; simpl.
      * eapply bisim_both. apply CIH. apply eta_match_1. 
      * eapply bisim_both. apply CIH. apply eta_match_2.
    + rewrite ! run_Bind_Later.
      eapply bisim_both. apply CIH. apply eta_match_2.
    + rewrite ! run_Bind_Bind.
      eapply bisim_both. apply CIH.
      apply eta_match_2 with (k0 := Kbind m0 k).
Qed.

Lemma Mon_law_2:
  forall (A: Type) (m: mon A), run (Bind m (@Ret A)) == run m.
Proof.
  intros. eapply bisim_equi. apply Mon_law_2_aux. apply eta_match_1.
Qed.

(** It follows that the denotation of a [Bind] is the [bind] of the
    denotations. *)

Lemma run_Bind_aux:
  forall (A B C: Type) (m: mon A) (k: cont A B) (f: B -> mon C),
  run (Bind m (insert_cont k f)) ==
  bind (run (Bind m (insert_cont k (@Ret _)))) (fun x => run (f x)).
Proof.
  cofix CIH; intros.
  destruct m.
  - rewrite ! run_Bind_Ret. destruct k; cbn.
    + rewrite run_Ret, bind_later, bind_now.
      constructor. apply equi_sym; apply eq_later.
    + rewrite bind_later. apply equi_later. apply CIH.
  - rewrite ! run_Bind_Later, bind_later.
    apply equi_later. apply CIH.
  - rewrite ! run_Bind_Bind, bind_later. 
    apply equi_later. apply CIH with (k := Kbind m0 k).
Qed.

Theorem run_Bind:
  forall (A B: Type) (m: mon A) (f: A -> mon B),
  run (Bind m f) == bind (run m) (fun x => run (f x)).
Proof.
  intros. 
  change (Bind m f) with (Bind m (insert_cont (K0 _) f)).
  eapply equi_trans. apply run_Bind_aux. apply bind_context. 
  apply Mon_law_2.
  intros; apply equi_refl.
Qed.

(** ** 6.7.  Application: an interpreter / denotational semantics for IMP *)

CoFixpoint cinterp (c: com) (s: store) : mon store :=
  match c with
  | SKIP => Ret s
  | ASSIGN x a => Ret (update x (aeval a s) s)
  | SEQ c1 c2 => Bind (cinterp c1 s) (cinterp c2)
  | IFTHENELSE b c1 c2 =>
      Later (cinterp (if beval b s then c1 else c2) s)
  | WHILE b c =>
      if beval b s then Bind (cinterp c s) (cinterp (WHILE b c))
                   else Ret s
  end.

(** The denotation of a command is the execution of its interpretation. *)

Definition denot (c: com) (s: store) : delay store := run (cinterp c s).

(** The denotational equations for IMP are satisfied, up to equitermination. *)

Lemma denot_skip: forall s,
  denot SKIP s == now s.
Proof.
  intros. unroll_delay (denot SKIP s). apply equi_refl.
Qed.

Lemma denot_assign: forall x a s,
  denot (ASSIGN x a) s == now (update x (aeval a s) s).
Proof.
  intros. unroll_delay (denot (ASSIGN x a) s). apply equi_refl.
Qed.

Lemma denot_seq: forall c1 c2 s,
  denot (SEQ c1 c2) s == bind (denot c1 s) (denot c2).
Proof.
  unfold denot; intros. rewrite (u_mon (cinterp (c1;;c2) s)); cbn.
  apply run_Bind.
Qed.

Lemma denot_ifthenelse: forall b c1 c2 s,
  denot (IFTHENELSE b c1 c2) s == if beval b s then denot c1 s else denot c2 s.
Proof.
  unfold denot; intros. rewrite (u_mon (cinterp (IFTHENELSE b c1 c2) s)); cbn.
  rewrite run_Later. destruct (beval b s); apply eq_later.
Qed.

Lemma denot_while: forall b c s,
  denot (WHILE b c) s ==
  if beval b s then bind (denot c s) (denot (WHILE b c)) else now s.
Proof.
  unfold denot; intros. rewrite (u_mon (cinterp (WHILE b c) s)); cbn.
  destruct (beval b s).
- apply run_Bind.
- rewrite run_Ret. apply equi_refl.
Qed.


