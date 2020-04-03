Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.

Definition dec (x y : nat) : x = y \/ x <> y.
  remember (x =? y).
  destruct b.
  * left. apply beq_nat_true. intuition.
  * right. apply beq_nat_false. intuition.
Qed.

Definition DeBruijnIndex := nat.

Inductive type :=
| TNat
| TAbs (t1 : type) (t2 : type)
| TBox (t : type).

Inductive pattrn :=
| PNatLit (n : nat)
| PBindVar (T : type)
| PBindApp (T1 T2 : type)
| PBindLam (T : type)
.

Inductive typedterm :=
| TypedTerm (u: term) (t: type)
with term :=
| Nat (n : nat)
| VAR (x : DeBruijnIndex)
| Lam (argT: type) (ebody : typedterm)
| App (e1 e2 : typedterm)
| Lift (e: typedterm)
| PatternMatch (e : typedterm) (pat : pattrn) (success failure : typedterm)
.
Notation "u ':' T" := (TypedTerm u T) (at level 49).

(* TODO resolve this name conflict in a better way *)
Instance var_term : Var term := {
                                 var := VAR
                               }.

Definition pattern_binders_count (pat : pattrn) : nat :=
  match pat with
  | PNatLit _ => 0
  | PBindVar _ => 1
  | PBindApp _ _ => 2
  | PBindLam _ => 1
  end.

Fixpoint traverse_typedterm (f : nat -> nat -> term) l t :=
  match t with
  | u : T => TypedTerm (traverse_term f l u) T
  end
with traverse_term f l u :=
  match u with
  | Nat n => Nat n
  | VAR x => f l x
  | Lam argT ebody => Lam argT (traverse_typedterm f (1 + l) ebody)
  | App e1 e2 => App (traverse_typedterm f l e1) (traverse_typedterm f l e2)
  | Lift e => Lift (traverse_typedterm f l e)
  | PatternMatch e pat success failure =>
    PatternMatch (traverse_typedterm f l e) pat (traverse_typedterm f (pattern_binders_count pat + l) success) (traverse_typedterm f l failure)
  end.

Compute (Nat 0 : TNat).

Instance Traverse_t_tt : Traverse term typedterm := {
  traverse := traverse_typedterm
}.

Instance Traverse_t_t : Traverse term term := {
  traverse := traverse_term
                                             }.
Lemma traverse_term_injective:
  forall f,
  (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) ->
  forall (t1 t2 : term) l,
  traverse_var f l t1 = traverse_var f l t2 ->
  t1 = t2

with traverse_typedterm_injective:
  forall f,
  (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) ->
  forall (t1 t2 : typedterm) l,
  traverse_var f l t1 = traverse_var f l t2 ->
  t1 = t2.
Proof.
  prove_traverse_var_injective.
  prove_traverse_var_injective.
Qed.

Instance TraverseVarInjective_term_typedterm :
  @TraverseVarInjective term _ typedterm _.
Proof.
  constructor. apply traverse_typedterm_injective.
Qed.
Instance TraverseVarInjective_term_term :
  @TraverseVarInjective term _ term _.
Proof.
  constructor. apply traverse_term_injective.
Qed.

Lemma traverse_functorial_value_value:
  forall f g (t : term) l,
  traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t

with traverse_functorial_value_term:
  forall f g (t : typedterm) l,
  traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t.
Proof.
  prove_traverse_functorial.
  prove_traverse_functorial.
Qed.

Instance TraverseFunctorial_term_term : @TraverseFunctorial term _ term _.
Proof. constructor. apply traverse_functorial_value_value. Qed.

Instance TraverseFunctorial_typedterm_typedterm : @TraverseFunctorial term _ typedterm _.
Proof. constructor. apply traverse_functorial_value_term. Qed.

Instance TraverseIdentifiesVar_term : TraverseIdentifiesVar.
Proof. constructor. prove_traverse_identifies_var. Qed.

Lemma traverse_relative_term_term:
  forall f g p (t : term) m l,
  (forall l x, f (l + p) x = g l x) ->
  m = l + p ->
  traverse f m t =
  traverse g l t

with traverse_relative_term_typedterm:
  forall f g p (t : typedterm) m l,
  (forall l x, f (l + p) x = g l x) ->
  m = l + p ->
  traverse f m t =
  traverse g l t.
Proof.
  prove_traverse_relative.
  prove_traverse_relative.
Qed.

Instance TraverseRelative_term_term : @TraverseRelative term term _.
Proof.
  constructor. apply traverse_relative_term_term.
Qed.

Instance TraverseRelative_term_typedterm : @TraverseRelative term typedterm _.
Proof.
  constructor. apply traverse_relative_term_typedterm.
Qed.

Lemma traverse_term_var_is_identity:
  forall f,
  (forall l x, f l x = var x) ->
  forall (t : term) l,
  traverse f l t = t

with traverse_typedterm_var_is_identity:
  forall f,
  (forall l x, f l x = var x) ->
  forall (t : typedterm) l,
  traverse f l t = t.
Proof.
  prove_traverse_var_is_identity.
  prove_traverse_var_is_identity.
Qed.

Instance TraverseVarIsIdentity_term_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. apply traverse_term_var_is_identity.
Qed.

Instance TraverseVarIsIdentity_term_typedterm : @TraverseVarIsIdentity term _ typedterm _.
Proof.
  constructor. apply traverse_typedterm_var_is_identity.
Qed.

Lemma test1 : subst (Nat 0) 0 (VAR 0 : TNat) = (Nat 0 : TNat).
  auto.
Qed.

Lemma lam_is_sane :
  (subst (Nat 42) 0 (Lam TNat (VAR 0 : TNat) : TAbs TNat TNat)) = Lam TNat (VAR 0 : TNat) : TAbs TNat TNat
/\ (subst (Nat 42) 0 (Lam TNat (VAR 1 : TNat) : TAbs TNat TNat)) = Lam TNat (Nat 42 : TNat) : TAbs TNat TNat
/\ (subst (Nat 42) 0 (Lam TNat (VAR 2 : TNat) : TAbs TNat TNat)) = Lam TNat (VAR 1 : TNat) : TAbs TNat TNat.
  auto.
Qed.

(* TODO add 'unit test' lemmas *)