Require Import String.
Require Import Coq.Program.Equality.

Definition string_eq (x y: string) : bool :=
  match string_dec x y with
    | left _  => true
    | right _ => false
  end.

Inductive Tipe : Set :=
  | t_bool : Tipe
  | t_lamb : Tipe -> Tipe -> Tipe.

Notation "A :-> B" := (t_lamb A B) (at level 70).

Inductive Term : Set :=
  | true  : Term
  | false : Term
  | ifte  : Term -> Term -> Term -> Term
  | var   : string -> Term
  | lamb  : string -> Term -> Term
  | app   : Term -> Term -> Term.

Inductive Ctx : Set :=
  | empty : Ctx
  | cons  : Ctx -> string -> Tipe -> Ctx.

Fixpoint ctx_lookup (G: Ctx) (x: string) : option Tipe :=
  match G with
    | empty => None
    | cons G y A =>
      if string_eq x y then Some(A) else ctx_lookup G x
  end.

Inductive Subs : Set :=
  | empty_subs : Subs
  | cons_subs  : Subs -> string -> Term -> Subs.

Fixpoint subs_lookup (g: Subs) (x: string) : option Term :=
  match g with
    | empty_subs => None
    | cons_subs g y a =>
      if string_eq x y then Some a else subs_lookup g x
  end.

Fixpoint without (g: Subs) (x: string) : Subs :=
  match g with
    | empty_subs => empty_subs
    | cons_subs g y a =>
      if string_eq x y
      then without g x
      else cons_subs (without g x) y a
  end.

Fixpoint subs1 (x: string) (s: Term) (t: Term) : Term :=
  match t with
    | var y      =>
      if string_eq x y then s else t
    | true       => true
    | false      => false
    | ifte a b c => ifte (subs1 x s a) (subs1 x s b) (subs1 x s c)
    | app f a    => app  (subs1 x s f) (subs1 x s a)
    | lamb y b   =>
      if string_eq x y then t else lamb y (subs1 x s b)
  end.

Fixpoint subs (g: Subs) (t: Term) : Term :=
  match t with
    | var x      =>
      match subs_lookup g x with
        | None   => var x
        | Some a => a
      end
    | true       => true
    | false      => false
    | ifte a b c => ifte (subs g a) (subs g b) (subs g c)
    | app f a    => app  (subs g f) (subs g a)
    | lamb x b   =>
      lamb x (subs (without g x) b)
  end.

Inductive Judgement : Set :=
  judgement : Ctx -> Term -> Tipe -> Judgement.

Notation "[ G |- a @ A ]" := (judgement G a A).

Inductive Deriv : Judgement -> Prop :=
  | d_true  : forall G: Ctx, Deriv [G |- true @ t_bool]
  | d_false : forall G: Ctx, Deriv [G |- false @ t_bool]
  | d_if    : forall G: Ctx,
              forall cond consq alt: Term,
              forall A: Tipe,
                   Deriv [G |- cond  @ t_bool]
                -> Deriv [G |- consq @ A]
                -> Deriv [G |- alt   @ A]
                -> Deriv [G |- ifte cond consq alt @ A]
  | d_var   : forall G: Ctx,
              forall x: string,
              forall A: Tipe,
                ctx_lookup G x = Some(A)
                -> Deriv [G |- (var x) @ A]
  | d_lamb  : forall G: Ctx,
              forall x: string,
              forall b: Term,
              forall A B: Tipe,
                Deriv [cons G x A |- b @ B]
                -> Deriv [G |- lamb x b @ A :-> B]
  | d_app   : forall G: Ctx,
              forall f a : Term,
              forall A B : Tipe,
                   Deriv [G |- f @ A :-> B]
                -> Deriv [G |- a @ A]
                -> Deriv [G |- app f a @ B].

Notation "# D" := (Deriv D) (at level 70).

Inductive Value : Set :=
  | v_true  : Value
  | v_false : Value
  | v_lamb  : string -> Term -> Value.
  
Inductive Step : Term -> Term -> Prop :=
  | step_true  : forall a b, Step (ifte true a b) a
  | step_false : forall a b, Step (ifte false a b) b
  | step_app   : forall v a b, Step (app (lamb v b) a) (subs1 v a b).

Inductive Halts : Term -> Tipe -> Prop :=
  | h_true :  Halts true t_bool
  | h_false : Halts false
  | h_lamb :  forall x b, Halts (lamb x b)
  | h_step :  forall a b, Step a b -> Halts b -> Halts a.

Lemma halt_if: forall a b c,
                 Halts a -> Halts b -> Halts c -> Halts (ifte a b c).
Proof.
  intros.
  induction H.
  - eapply h_step. apply step_true. assumption.
  - eapply h_step. apply step_false. assumption.
  -.


Fixpoint SN (a: Term) (A: Tipe) : Prop :=
  match A with
    | t_bool  =>
      #[empty |- a @ t_bool]
      /\ Halts a A
    | A :-> B =>
        #[empty |- a @ A :-> B]
        /\ Halts a A
        /\ (forall b, SN b A -> SN (app a b) B)
  end.

Lemma sn__halt: forall a A, SN a A -> Halt a.
Proof.
  intros.
  destruct A; unfold SN in H.
  { destruct H; destruct a; assumption. }
  { simpl in H; fold SN in H.
    destruct H; destruct H0; assumption. }
Qed.

Lemma sn__type: forall a A, SN a A -> #[empty |- a @ A].
Proof.
  intros.
  destruct A; unfold SN in H; destruct H; assumption.
Qed.

Definition subs_matches_ctx (g: Subs) (G: Ctx) : Prop :=
  forall x a A, subs_lookup g x = Some a /\
                ctx_lookup  G x = Some A /\
                SN a A.

Notation "g |= G" := (subs_matches_ctx g G) (at level 70).

Lemma sn_ind: forall g G a A,
                #[G |- a @ A] -> g |= G -> SN (subs g a) A.
Proof.
  intros.
  dependent induction H; simpl.
  { split. apply d_true. apply halt_true. }
  { split. apply d_false. apply halt_false. }
  { intuition. destruct A; simpl; split.
    { apply sn__type in H3. apply sn__type in H4.
      apply d_if; try assumption.
      apply sn__type.
      eapply IHDeriv1. reflexivity. assumption. }
    { apply sn__halt in H3. apply sn__halt in H4.
      




Theorem strong_normalization: forall a A, #[empty |- a @ A] -> Halt a.
Proof.
  intros.