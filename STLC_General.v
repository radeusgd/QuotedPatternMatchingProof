Require Import String.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Omega.

Definition label := nat.

Inductive TType :=
| TNat : TType
| TLam : TType -> TType -> TType.

Inductive Term :=
| Val : Value -> Term
| Var : label -> Term
| App : Term -> Term -> Term
with Value :=
| Lit : nat -> Value
| Lam : label -> TType -> Term -> Value.

Inductive TypCtx :=
| Tempty : TypCtx
| Textend : TypCtx -> label -> TType -> TypCtx.

Notation "G ';' x ':' T" := (Textend G x T) (at level 40, x at level 59).
Notation "∅" := Tempty.

Inductive Tcontains : TypCtx -> label -> TType -> Prop :=
| tcontains_head : forall G x T, Tcontains (G; x : T) x T
| tcontains_cons : forall G x' T' x T, Tcontains G x T -> x' <> x -> Tcontains (G; x' : T') x T.

Definition rho := (∅; 0 : TNat; 1 : TNat).
Ltac solveTcontains :=
  (try apply tcontains_head); try (apply tcontains_cons; solveTcontains; auto).
Theorem test_contains : Tcontains rho  1 TNat /\ Tcontains rho 0 TNat.
  unfold rho; split; solveTcontains.
Qed.

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Inductive term_typing : TypCtx -> Term -> TType -> Prop :=
| ty_lit : forall G n, G ⊢ (Val (Lit n)) : TNat
| ty_var : forall G x t, Tcontains G x t -> G ⊢ Var x : t
| ty_lam : forall G arg argT body bodyT, (G; arg : argT) ⊢ body : bodyT -> G ⊢ (Val (Lam arg argT body)) : (TLam argT bodyT)
| ty_app : forall G f arg argT retT, G ⊢ f : (TLam argT retT) -> G ⊢ arg : argT -> G ⊢ (App f arg) : retT
where "G '⊢' t ':' T" := (term_typing G t T).

Inductive is_free_in : label -> Term -> Prop :=
| fv_var : forall x, is_free_in x (Var x)
| fv_app1 : forall x t1 t2, is_free_in x t1 -> is_free_in x (App t1 t2)
| fv_app2 : forall x t1 t2, is_free_in x t2 -> is_free_in x (App t1 t2)
| fv_lam : forall x y t T, is_free_in x t -> x <> y -> is_free_in x (Val (Lam y T t))
.

Definition closed (t: Term): Prop := forall x, not (is_free_in x t).

Inductive is_present_in : label -> Term -> Prop :=
| isi_var : forall x, is_present_in x (Var x)
| isi_lam_arg : forall x T b, is_present_in x (Val (Lam x T b))
| isi_lam_body : forall y x T b, is_present_in y b -> is_present_in y (Val (Lam x T b))
| isi_app1 : forall x t1 t2, is_present_in x t1 -> is_present_in x (App t1 t2)
| isi_app2 : forall x t1 t2, is_present_in x t2 -> is_present_in x (App t1 t2)
.

Fixpoint fresh (term: Term) : label :=
  match term with
  | Val (Lit n) => 0
  | Val (Lam x T t) => max x (fresh t + 1)
  | Var x => x + 1
  | App t1 t2 => max (fresh t1) (fresh t2)
  end.

Lemma freshReturnsGreaterThanAll : forall t x, is_present_in x t -> fresh t > x.
  induction t; intros.
  * destruct v.
    ** exfalso.
       inversion H.
    **
Admitted.

Definition fresh2 (t1: Term) (t2: Term) := (max (fresh t1) (fresh t2)) + 1.

Fixpoint renameVars (term: Term) (old: label) (new: label): Term :=
  match term with
  | Val (Lit n) => term
  | Val (Lam x T t) =>
    if Nat.eq_dec x old then Val (Lam new T (renameVars t old new))
    else Val (Lam x T (renameVars t old new))
  | Var x =>
    if Nat.eq_dec x old then Var new
    else term
  | App t1 t2 => App (renameVars t1 old new) (renameVars t2 old new)
end.

Fixpoint termSize (term: Term) : nat :=
  match term with
  | Val (Lit n) => 1
  | Val (Lam x T t) => 1 + termSize t
  | Var x => 1
  | App t1 t2 => 1 + (termSize t1) + (termSize t2)
  end.

Require Coq.Program.Wf.
Program Fixpoint substitute (term: Term) (varname: label) (varterm: Term) {measure 0 termSize} : Term :=
  match term with
  | Val (Lit n) => term
  | Val (Lam x T t) =>
    if Nat.eq_dec x varname then term
    else
      let freshx := fresh2 varterm t in
      let t' := renameVars t x freshx in
      Val (Lam freshx T (substitute t' varname varterm))
  | Var x =>
    if Nat.eq_dec x varname then varterm
    else term
  | App t1 t2 => App (substitute t1 varname varterm) (substitute t2 varname varterm)
  end.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive reduces : Term -> Term -> Prop :=
| red_beta : forall argname argT body arg, (App (Val (Lam argname argT body)) arg) --> (substitute body argname arg)
| red_app1 : forall t1 t1' t2, t1 --> t1' -> (App t1 t2) --> (App t1' t2)
| red_app2 : forall t1 t2 t2', t2 --> t2' -> (App t1 t2) --> (App t1 t2')
where "t1 '-->' t2" := (reduces t1 t2).

Definition lam_id := Val (Lam (0) (TNat) (Var 0)).
Lemma id_typ : ∅ ⊢ lam_id : (TLam TNat TNat).
unfold lam_id.
apply ty_lam.
apply ty_var. solveTcontains.
Qed.
Definition app_id := (App lam_id (Val (Lit 1))).
Lemma app1 : ∅ ⊢ app_id : TNat.
eapply ty_app with TNat.
* apply id_typ.
* apply ty_lit.
Qed.
Lemma app_red : app_id --> Val (Lit 1).
  unfold app_id.
  apply red_beta.
Qed.

Inductive isValue : Term -> Prop :=
| valisval : forall v, isValue (Val v).

Lemma emptyEnvHasNoVars1 : forall x T, Tcontains ∅ x T -> False.
  intros.
  inversion H.
Qed.
Lemma emptyEnvHasNoVars2 : forall x T, ∅ ⊢ Var x : T -> False.
  intros.
  inversion H.
  apply emptyEnvHasNoVars1 in H2.
  contradiction.
Qed.
Lemma litIsNotFun : forall T1 T2 n, ∅ ⊢ Val (Lit n) : TLam T1 T2 -> False.
  intros.
  inversion H.
Qed.

Theorem Progress : forall t T, ∅ ⊢ t : T -> isValue t \/ exists t', t --> t'.
  induction t.
  intros.
  * left. apply valisval.
  *
    intros.
    apply emptyEnvHasNoVars2 in H.
    contradiction.
  * right.
    inversion H.
    remember H3 as t1isLambda. clear Heqt1isLambda.
    apply IHt1 in H3.
    destruct H3.
    **
      inversion H3.
      destruct v.
      ***
        assert (∅ ⊢ Val (Lit n) : TLam argT T).
        **** rewrite -> H6. assumption.
        **** apply litIsNotFun in H7.
             contradiction.
      ***
        exists (substitute t0 l t2).
        apply red_beta.
    **
      inversion H3.
      exists (App x t2).
      apply red_app1. assumption.
Qed.

(* Lemma free_in_context : forall G x t T, *)
(*     is_free_in x t -> G ⊢ t : T -> exists T', Tcontains G x T'. *)
(*   intros. *)
(*   induction t. *)

(* Admitted. *)

(* Corollary typableInEmptyIsClosed : forall t T, ∅ ⊢ t : T -> closed t. *)
(*   intros. *)
(*   unfold closed. *)
(*   intros. intro. *)
(*   assert (exists T', Tcontains ∅ x T'). *)
(*   * apply free_in_context with t T; auto. *)
(*   * inversion H1. *)
(*     rename x0 into T'. *)
(*     inversion H2. *)
(* Qed. *)

Lemma Weakening : forall G G' t T,
    G ⊢ t : T -> (forall x T', is_free_in x t -> Tcontains G x T' <-> Tcontains G' x T') -> G' ⊢ t : T.
  intros.

Admitted.

Lemma CanonicalForm1 : forall G v, G ⊢ (Val v) : TNat -> exists n, v = Lit n.
  intros.
  inversion H.
  exists n.
  trivial.
Qed.
Lemma CanonicalForm2 : forall G v T1 T2, G ⊢ (Val v) : TLam T1 T2 -> exists x t, v = Lam x T1 t.
  intros.
  inversion H.
  exists arg. exists body.
  trivial.
Qed.

Lemma Substitution : forall G t1 T1 x t2 T2, G ⊢ t1 : T1 /\ G ; x : T1 ⊢ t2 : T2 -> G ⊢ substitute t2 x t1 : T2.
  induction t2; intros; inversion H.
  * 
(*
  * simpl.
  intros.
  inversion H.
*)
Admitted.

Lemma AppIsApp : forall G t1 t2 T, G ⊢ App t1 t2 : T -> exists T', (G ⊢ t1 : TLam T' T) /\ (G ⊢ t2 : T').
  intros.
  inversion H.
  exists argT.
  auto.
Qed.

Theorem Preservation : forall G t T t', G ⊢ t : T /\ t --> t' -> G ⊢ t' : T.
  induction t; intros; inversion H; inversion H1.
  * apply Substitution with argT.
    assert (Ht : G ⊢ App (Val (Lam argname argT body)) t2 : T).
    rewrite H3. auto.
    intuition.
    ** inversion Ht.
       assert (argT0 = argT).
       *** inversion H9. trivial.
       *** rewrite <- H12. trivial.
    ** inversion Ht.
       inversion H9. trivial.
  * inversion H0.
    apply ty_app with argT.
    ** apply IHt1. intuition.
    ** trivial.
  * inversion H0.
    apply ty_app with argT.
    ** trivial.
    ** apply IHt2. intuition.
Qed.
