Require Import Autosubst.Autosubst.

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

Inductive step : term -> term -> Prop :=
| Step_beta (s1 s2 t : term) :
    s1.[t/] = s2 -> step (App (Lam s1) t) s2
| Step_appL (s1 s2 t : term) :
    step s1 s2 -> step (App s1 t) (App s2 t)
| Step_appR (s t1 t2 : term) :
    step t1 t2 -> step (App s t1) (App s t2)
| Step_lam (s1 s2 : term) :
    step s1 s2 -> step (Lam s1) (Lam s2).
Hint Constructors step.

Lemma substitutivity s1 s2 :
  step s1 s2 -> forall sigma, step s1.[sigma] s2.[sigma].
  intro.
  induction H; constructor; subst; autosubst.
Qed.

Inductive type :=
| Nat
| Arr (A B : type).

Reserved Notation "G '⊢' t ':' T" (at level 40, t at level 59).
Inductive ty (Γ : var -> type) : term -> type -> Prop :=
| Ty_Lit n : Γ ⊢ (Lit n) : Nat
| Ty_Var x A : Γ x = A ->
                   Γ ⊢ (Var x) : A
| Ty_Lam s A B : (A .: Γ) ⊢ s : B ->
                   Γ ⊢ (Lam s) : (Arr A B)
| Ty_App s t A B : Γ ⊢ s : (Arr A B) -> Γ ⊢ t : A ->
                   Γ ⊢ (App s t) : B
where "G '⊢' t ':' T" := (ty G t T).
Hint Constructors ty.

Lemma ty_ren G s A:
  ty G s A -> forall Delta xi,
  G = xi >>> Delta ->
  ty Delta s.[ren xi] A.
Proof.
  induction 1; intros; subst; asimpl; econstructor; eauto.
  - eapply IHty. autosubst.
Qed.

Lemma ty_subst : forall G s A,
  G ⊢ s : A -> forall sigma Delta,
  (forall x, Delta ⊢ (sigma x) : (G x)) ->
  Delta ⊢ s.[sigma] : A.
Proof.
  induction 1; intros; subst; asimpl; eauto using ty.
  - econstructor. eapply IHty.
    intros [|]; asimpl; eauto using ty, ty_ren.
Qed.

Inductive reduces : term -> term -> Prop :=
| onestep (t1 t2 : term) : step t1 t2 -> reduces t1 t2
| transitive (t1 t2 t3 : term) : step t1 t2 -> reduces t2 t3 -> reduces t1 t3.
Hint Constructors reduces.

Definition lamid := (Lam (Var 0)).
Lemma test1 : reduces (App lamid (Lit 42)) (Lit 42).
  apply onestep.
  constructor. autosubst.
Qed.
Eval simpl in (Var 0).[ids].
Notation "∅" := ids.

Theorem ty_preservation : forall G s A,
  G ⊢ s : A -> forall s',
  step s s' ->
  G ⊢ s' : A.
Proof.
Admitted.

Inductive isValue : term -> Prop :=
| LitIsVal : forall n, isValue (Lit n)
| LamIsVal : forall t, isValue (Lam t).

(* TODO *)
Theorem progress : forall s A,
    ids 0 ⊢ s : A -> isValue s \/ exists s', step s s'.
