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

(*
There are no free variables in well-typed terms (all should be bound to some λ), so we don't have to worry about avoiding capture.
(TODO is that correct?)
*)
Fixpoint substitute (term: Term) (varname: label) (varterm: Term) : Term :=
  match term with
  | Val (Lit n) => term
  | Val (Lam x T t) =>
    if Nat.eq_dec x varname then term
    else term (* TODO *)
  | Var x =>
    if Nat.eq_dec x varname then varterm
    else term
  | App t1 t2 => App (substitute t1 varname varterm) (substitute t2 varname varterm)
  end.

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
