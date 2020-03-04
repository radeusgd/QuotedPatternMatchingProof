Require Import String.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Omega.
Require Coq.Arith.EqNat.

Definition label := nat.

Inductive TType :=
| TNat : TType
| TLam : TType -> TType -> TType.

Inductive Term :=
| Lit : nat -> Term
| Lam : label -> TType -> Term -> Term
| Var : label -> Term
| App : Term -> Term -> Term
.

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
| ty_lit : forall G n, G ⊢ (Lit n) : TNat
| ty_var : forall G x t, Tcontains G x t -> G ⊢ Var x : t
| ty_lam : forall G arg argT body bodyT, (G; arg : argT) ⊢ body : bodyT -> G ⊢ (Lam arg argT body) : (TLam argT bodyT)
| ty_app : forall G f arg argT retT, G ⊢ f : (TLam argT retT) -> G ⊢ arg : argT -> G ⊢ (App f arg) : retT
where "G '⊢' t ':' T" := (term_typing G t T).
Hint Constructors term_typing.
(*
There are no free variables in well-typed terms (all should be bound to some λ), so we don't have to worry about avoiding capture.
(TODO is that correct?)
*)
Fixpoint substitute (term: Term) (varname: label) (varterm: Term) : Term :=
  match term with
  | Lit n => term
  | Lam x T t =>
    if Nat.eqb x varname then term
    else Lam x T (substitute t varname varterm)
  | Var x =>
    if Nat.eqb x varname then varterm
    else term
  | App t1 t2 => App (substitute t1 varname varterm) (substitute t2 varname varterm)
  end.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive reduces : Term -> Term -> Prop :=
| red_beta : forall argname argT body arg, (App (Lam argname argT body) arg) --> (substitute body argname arg)
| red_app1 : forall t1 t1' t2, t1 --> t1' -> (App t1 t2) --> (App t1' t2)
| red_app2 : forall t1 t2 t2', t2 --> t2' -> (App t1 t2) --> (App t1 t2')
where "t1 '-->' t2" := (reduces t1 t2).

Definition lam_id := (Lam (0) (TNat) (Var 0)).
Lemma id_typ : ∅ ⊢ lam_id : (TLam TNat TNat).
  unfold lam_id.
  apply ty_lam.
  apply ty_var. solveTcontains.
Qed.
Definition app_id := (App lam_id (Lit 1)).
Lemma app1 : ∅ ⊢ app_id : TNat.
eapply ty_app with TNat.
* apply id_typ.
* apply ty_lit.
Qed.
Lemma app_red : app_id --> (Lit 1).
  unfold app_id.
  apply red_beta.
Qed.

Inductive isValue : Term -> Prop :=
| litisval : forall n, isValue (Lit n)
| lamisval : forall x T t, isValue (Lam x T t).

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
Lemma litIsNotFun : forall G T1 T2 n, G ⊢ (Lit n) : TLam T1 T2 -> False.
  intros.
  inversion H.
Qed.
Lemma lamIsFun : forall G x Targ t Tres, G ⊢ Lam x Targ t : Tres -> exists T1 T2, Tres = TLam T1 T2.
  intros.
  inversion H.
  exists Targ. exists bodyT.
  auto.
Qed.

Theorem Progress : forall t T, ∅ ⊢ t : T -> isValue t \/ exists t', t --> t'.
  induction t.
  intros.
  * left. apply litisval.
  * left. apply lamisval.
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
      ***
        assert (∅ ⊢ (Lit n) : TLam argT T).
        rewrite H6. assumption.
        apply litIsNotFun in H7.
        contradiction.
      ***
        exists (substitute t x t2).
        apply red_beta.
    **
      inversion H3.
      exists (App x t2).
      apply red_app1. assumption.
Qed.

Inductive is_free_in : label -> Term -> Prop :=
| fv_var : forall x, is_free_in x (Var x)
| fv_app1 : forall x t1 t2, is_free_in x t1 -> is_free_in x (App t1 t2)
| fv_app2 : forall x t1 t2, is_free_in x t2 -> is_free_in x (App t1 t2)
| fv_lam : forall x y t T, is_free_in x t -> x <> y -> is_free_in x (Lam y T t)
.

Definition closed (t: Term): Prop := forall x, not (is_free_in x t).

Lemma free_in_context : forall G x t T,
    is_free_in x t -> G ⊢ t : T -> exists T', Tcontains G x T'.
  intros.
  induction t.

Admitted.

Corollary typableInEmptyIsClosed : forall t T, ∅ ⊢ t : T -> closed t.
  intros.
  unfold closed.
  intros. intro.
  assert (exists T', Tcontains ∅ x T').
  * apply free_in_context with t T; auto.
  * inversion H1.
    rename x0 into T'.
    inversion H2.
Qed.

Lemma CanonicalForm1 : forall G t, G ⊢ t : TNat -> isValue t -> exists n, t = Lit n.
  intros.
  inversion H0.
  * exists n. trivial.
  * rewrite <- H1 in H.
    inversion H.
Qed.
Lemma CanonicalForm2 : forall G t T1 T2, G ⊢ t : TLam T1 T2 -> isValue t -> exists x t', t = Lam x T1 t'.
  intros.
  inversion H0.
  * rewrite <- H1 in H.
    inversion H.
  * exists x. exists t0.
    assert (T = T1).
    ** rewrite <- H1 in H.
       inversion H. trivial.
    ** rewrite H2. trivial.
Qed.

Lemma Weakening : forall G G' t T,
    G ⊢ t : T -> (forall x T', is_free_in x t -> Tcontains G x T' <-> Tcontains G' x T') -> G' ⊢ t : T.
  intros.

Admitted.

Lemma IndependentEnvOrder : forall t T G x1 T1 x2 T2, x1 <> x2 -> (G ; x1 : T1; x2 : T2) ⊢ t : T -> (G ; x2 : T2; x1 : T1) ⊢ t : T.
  intros.
  eapply Weakening.
  exact H0.
  intros.
  intuition; inversion H2.
  * solveTcontains. intuition.
  * 

Admitted.
(* Lemma SimpleWeakening : forall G t T x T', *)

Lemma Substitution : forall t2 G t1 T1 x T2, ∅ ⊢ t1 : T1 /\ G ; x : T1 ⊢ t2 : T2 -> G ⊢ substitute t2 x t1 : T2.
  induction t2. intros; inversion H.
  * simpl.
    inversion H1.
    apply ty_lit.
  * simpl. intros.
    remember (l =? x) as Heq.
    destruct Heq.
    ** assert (l=x).
       apply beq_nat_true; intuition. intros. intuition.
       apply Weakening with (G; x : T1).
       trivial.
       intros.
       assert (x0 <> x).
       intro. rewrite H3 in H.
       inversion H. intuition.
       intuition.
       ****
         inversion H4.
         exfalso. apply H3. auto.
         trivial.
       ****
         apply tcontains_cons. trivial. auto.
    ** assert (l<>x).
       apply beq_nat_false; intuition.
       intros. intuition.
       destruct T2.
       ***
         exfalso.
         inversion H2.
       ***
         assert (t=T2_1).
         admit.
         rewrite H.
         apply ty_lam.
         apply IHt2 with T1.
         intuition.
         inversion H2.
         apply IndependentEnvOrder. auto. auto.
  * simpl. intros.
    remember (l =? x) as Heq.
    destruct Heq.
    ** assert (l = x).
       apply beq_nat_true; intuition. intros.
       intuition.
       assert ((G; x : T1) ⊢ Var x : T2).
       ***
         rewrite <- H0.
         rewrite <- H0 in H2.
         intuition.
       ***
         assert (T1 = T2).
         ****
           inversion H0.
           inversion H.
           inversion H6. trivial. intuition.
         ****
           rewrite <- H3.
           eapply Weakening. exact H1.
           intros.
           exfalso.
           assert (closed t1).
           ***** eapply typableInEmptyIsClosed. exact H1.
           ***** unfold closed in H5. apply H5 with x0. trivial.
    ** assert (l <> x).
       apply beq_nat_false. intuition. intros. intuition.
       apply Weakening with (G; x : T1).
  (*      trivial. *)
  (*      intros. *)
  (*      inversion H2. *)
  (*      intuition. *)
  (*      *** inversion H0. exfalso. intuition. trivial. *)
  (*      *** apply tcontains_cons; intuition. *)
       admit.
       admit.
  * simpl. intros. intuition.
    inversion H1.
    apply ty_app with argT.
    ** eapply IHt2_1.
       intuition. exact H0. intuition.
    ** eapply IHt2_2.
       intuition. exact H0. intuition.
Admitted.

Lemma AppIsApp : forall G t1 t2 T, G ⊢ App t1 t2 : T -> exists T', (G ⊢ t1 : TLam T' T) /\ (G ⊢ t2 : T').
  intros.
  inversion H.
  exists argT.
  auto.
Qed.

Theorem Preservation : forall t T t', ∅ ⊢ t : T /\ t --> t' -> ∅ ⊢ t' : T.
  induction t; intros; inversion H; inversion H1.
  * apply Substitution with argT.
    assert (Ht : ∅ ⊢ App (Lam argname argT body) t2 : T).
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
