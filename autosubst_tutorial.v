Require Import List Omega.
Require Import Autosubst.Autosubst.
Require Import Context.

Definition dec (x y : nat) : x = y \/ x <> y.
  remember (x =? y).
  destruct b.
  * left. apply beq_nat_true. intuition.
  * right. apply beq_nat_false. intuition.
Qed.

Inductive term :=
| Lit (n : nat)
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Goal forall sigma,
  (Lam (App (Var 0) (Var 3))).[sigma] = Lam (App (Var 0) (sigma 2).[ren(+1)]).
  intros. asimpl. reflexivity. Qed.

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : term -> term -> Prop :=
| Step_beta (s1 s2 t : term) :
    s1.[t/] = s2 -> (App (Lam s1) t) --> s2
| Step_appL (s1 s2 t : term) :
    s1 --> s2 -> (App s1 t) --> (App s2 t)
| Step_appR (s t1 t2 : term) :
    t1 --> t2 -> (App s t1) --> (App s t2)
(* | Step_lam (s1 s2 : term) : *)
(*     step s1 s2 -> step (Lam s1) (Lam s2). *)
where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step.

Lemma substitutivity s1 s2 :
  step s1 s2 -> forall sigma, step s1.[sigma] s2.[sigma].
  intro.
  induction H; constructor; subst; autosubst.
Qed.

Inductive type :=
| Nat
| Arr (A B : type).

Definition ctx := list type.

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Inductive ty (Γ : ctx) : term -> type -> Prop :=
| Ty_Lit n : Γ ⊢ (Lit n) : Nat
| Ty_Var x A : atn Γ x A ->
                   Γ ⊢ (Var x) : A
| Ty_Lam s A B : (A :: Γ) ⊢ s : B ->
                   Γ ⊢ (Lam s) : (Arr A B)
| Ty_App s t A B : Γ ⊢ s : (Arr A B) -> Γ ⊢ t : A ->
                   Γ ⊢ (App s t) : B
where "G '⊢' t ':' T" := (ty G t T).
Hint Constructors ty.

(* Lemma ty_ren G s A: *)
(*   ty G s A -> forall Delta xi, *)
(*   G = xi >>> Delta -> *)
(*   ty Delta s.[ren xi] A. *)
(* Proof. *)
(*   induction 1; intros; subst; asimpl; econstructor; eauto. *)
(*   - eapply IHty. autosubst. *)
(* Qed. *)

(* Lemma ty_subst : forall G s A, *)
(*   G ⊢ s : A -> forall sigma Delta, *)
(*   (forall x, Delta ⊢ (sigma x) : (G x)) -> *)
(*   Delta ⊢ s.[sigma] : A. *)
(* Proof. *)
(*   induction 1; intros; subst; asimpl; eauto using ty. *)
(*   - econstructor. eapply IHty. *)
(*     intros [|]; asimpl; eauto using ty, ty_ren. *)
(* Qed. *)


Inductive reduces : term -> term -> Prop :=
| onestep (t1 t2 : term) : step t1 t2 -> reduces t1 t2
| transitive (t1 t2 t3 : term) : step t1 t2 -> reduces t2 t3 -> reduces t1 t3.
Hint Constructors reduces.

Definition lamid := (Lam (Var 0)).
Lemma test1 : reduces (App lamid (Lit 42)) (Lit 42).
  apply onestep.
  constructor. autosubst.
Qed.
(* Definition emptyEnv (x : var) : option type := None. *)
Definition emptyEnv: ctx := nil.
Notation "∅" := emptyEnv.

Theorem EmptyEnvDefinesNoVars : forall x T, atn ∅ x T -> False.
  intros.
  inversion H.
Qed.

Inductive isValue : term -> Prop :=
| LitIsVal : forall n, isValue (Lit n)
| LamIsVal : forall t, isValue (Lam t).
Hint Constructors isValue.

Lemma CanonicalFormLam : forall G t A B, G ⊢ t : Arr A B -> isValue t -> exists s, t = Lam s /\ (A :: G) ⊢ s : B.
  intros.
  inversion H0.
  * rewrite <- H1 in H. inversion H.
  * exists t0.
    intuition.
    rewrite <- H1 in H.
    inversion H. trivial.
Qed.

Theorem Progress : forall t T, ∅ ⊢ t : T -> isValue t \/ exists t', t --> t'.
  induction t; intros; intuition.
  * exfalso.
    inversion H. inversion H1.
  * right.
    inversion H.
    assert (isValue t1 \/ (exists t' : term, t1 --> t')).
    apply IHt1 with (Arr A T). trivial.
    inversion H5.
    **
      eapply CanonicalFormLam in H6.
      2: exact H2.
      inversion H6. destruct H7.
      rewrite H7.
      exists (x.[t2/]).
      auto.
    ** inversion H6. eauto.
Qed.

Lemma SubstitutionGeneralized : forall (G1 G2 : ctx) (s: term) (A: type) (σ: var -> term),
    G1 ⊢ s : A -> (forall x B, atn G1 x B -> G2 ⊢ σ x : B) ->
             G2 ⊢ s.[σ] : A.
  Admitted.

Lemma Substitution : forall t2 G t1 T1 T2, G ⊢ t1 : T1 /\ (T1 :: G) ⊢ t2 : T2 -> G ⊢ t2.[t1/] : T2.
  intros.
  inversion H.
  eapply SubstitutionGeneralized.
  exact H1.
  intros.
  destruct x.
  * cbn in H2. subst.
    autosubst.
  * cbn in H2.
    assert (G ⊢ Var x : B).
    auto.
    autosubst.
Qed.

(* Lemma Substitution : forall t2 G t1 T1 T2, G ⊢ t1 : T1 /\ (T1 :: G) ⊢ t2 : T2 -> G ⊢ t2.[t1/] : T2. *)
(*   intro. *)
(*   induction t2; intros. *)
(*   * *)
(*     inversion H. *)
(*     inversion H1. *)
(*     autosubst. *)
(*   * inversion H. inversion H1. *)
(*     destruct x. *)
(*     ** *)
(*       cbn in H3. *)
(*       rewrite H3. *)
(*       autosubst. *)
(*     ** subst. *)
(*        assert ((Var (S x)).[t1/] = Var x). *)
(*        autosubst. *)
(*        rewrite H2. *)
(*        inversion H1. *)
(*        cbn in H5. *)
(*        auto. *)
(*   * assert ((App t2_1 t2_2).[t1/] = (App t2_1.[t1/] t2_2.[t1/])). *)
(*     autosubst. rewrite H0. *)
(*     inversion H. *)
(*     inversion H2. *)
(*     subst. *)
(*     apply Ty_App with A. *)
(*     ** apply IHt2_1 with T1. intuition. *)
(*     ** apply IHt2_2 with T1. intuition. *)
(*   * inversion H. *)
(*     inversion H1. *)
(*     apply Ty_Lam. *)
(*     subst. *)
(*     admit. *)
(*     (* apply IHt2 with T1. intuition. *) *)
(* Admitted. *)

Theorem Preservation : forall s A G,
  G ⊢ s : A -> forall s',
  s --> s' ->
  G ⊢ s' : A.
Proof.
  intro.
  induction s; intros.
  * inversion H0.
  * inversion H0.
  * inversion H0; inversion H; subst.
    **
      inversion H7. subst.
      eapply Substitution.
      eauto.
    **
      assert (G ⊢ s3 : Arr A0 A).
      apply IHs1. auto. auto.
      eauto.
    **
      assert (G ⊢ t2 : A0).
      apply IHs2. auto. auto.
      eauto.
  * inversion H0.
Qed.

