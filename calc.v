Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.

Definition dec (x y : nat) : x = y \/ x <> y.
  remember (x =? y).
  destruct b.
  * left. apply beq_nat_true. intuition.
  * right. apply beq_nat_false. intuition.
Qed.

(* SYNTAX *)

Definition DeBruijnIndex := nat.

Inductive type :=
| TNat
| TArr (T1 : type) (T2 : type)
| TBox (T : type).
Notation "'⧈' T" := (TBox T) (at level 48).
Notation "T1 '==>' T2" := (TArr T1 T2) (at level 48).

(* Inductive pattrn := *)
(* | PNatLit (n : nat) *)
(* | PBindVar (T : type) *)
(* | PBindApp (T1 T2 : type) *)
(* | PBindUnlift *)
(* | PBindLam (T : type) *)
(* . *)

Inductive typedterm :=
| TypedTerm (u: term) (t: type)
with term :=
| Nat (n : nat)
| VAR (x : DeBruijnIndex)
| Lam (argT: type) (ebody : typedterm)
| App (e1 e2 : typedterm)
| Lift (e: typedterm)
| Box (e : typedterm)
(* | PatternMatch (e : typedterm) (pat : pattrn) (success failure : typedterm) *)
.
Notation "u ':' T" := (TypedTerm u T) (at level 49).

(* TODO resolve this name conflict in a better way *)
Instance var_term : Var term := {
                                 var := VAR
                               }.

(* Definition pattern_binders_count (pat : pattrn) : nat := *)
(*   match pat with *)
(*   | PNatLit _ => 0 *)
(*   | PBindVar _ => 1 *)
(*   | PBindApp _ _ => 2 *)
(*   | PBindLam _ => 1 *)
(*   end. *)

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
  | Box e => Box (traverse_typedterm f l e)
  (* | PatternMatch e pat success failure => *)
  (*   PatternMatch (traverse_typedterm f l e) pat (traverse_typedterm f (pattern_binders_count pat + l) success) (traverse_typedterm f l failure) *)
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
  (subst (Nat 42) 0 (Lam TNat (VAR 0 : TNat) : TNat ==> TNat)) = Lam TNat (VAR 0 : TNat) : TNat ==> TNat
/\ (subst (Nat 42) 0 (Lam TNat (VAR 1 : TNat) : TNat ==> TNat)) = Lam TNat (Nat 42 : TNat) : TNat ==> TNat
/\ (subst (Nat 42) 0 (Lam TNat (VAR 2 : TNat) : TNat ==> TNat)) = Lam TNat (VAR 1 : TNat) : TNat ==> TNat.
  auto.
Qed.

Definition substitute (v : typedterm) (t : typedterm) : typedterm :=
  match v with
  | TypedTerm vt _ => subst vt 0 t
  end.

(* TYPES *)

Require Import Dblib.Environments.
Inductive Level := L0 | L1.
Definition TypEnv := env (Level * type).
Definition emptyEnv : env (Level * type) := empty (Level * type).
Notation "∅" := emptyEnv.
Definition extendEnv (G : TypEnv) (L : Level) (T : type) : TypEnv := (insert 0 (L, T) G).
(* Notation "G ';' L T" := (insert 0 (L, T) G) (at level 49). *)

Definition env_has (G : TypEnv) (x : DeBruijnIndex) (L : Level) (T : type) : Prop :=
  lookup x G = Some (L, T).

Reserved Notation "G '⊢(' L ')' t '∈' T" (at level 40, t at level 59).
Inductive typing_judgement : TypEnv -> Level -> typedterm -> type -> Prop :=
| T_Nat : forall L G n, G ⊢(L) (Nat n : TNat) ∈ TNat
| T_Var : forall L G x T,
    env_has G x L T ->
    G ⊢(L) (VAR x : T) ∈ T
| T_Abs : forall L G T1 T2 body,
    extendEnv G L T1 ⊢(L) body ∈ T2 ->
    G ⊢(L) (Lam T1 body : T1 ==> T2) ∈ (T1 ==> T2)
| T_App : forall L G T1 T2 t1 t2,
    G ⊢(L) t1 ∈ (T1 ==> T2) ->
    G ⊢(L) t2 ∈ T1 ->
    G ⊢(L) (App t1 t2: T2) ∈ T2
| T_Lift : forall G t, G ⊢(L0) t ∈ TNat -> G ⊢(L0) (Lift t : ⧈TNat) ∈ ⧈TNat
where "G '⊢(' L ')' t '∈' T" := (typing_judgement G L t T).
Hint Constructors typing_judgement : typing_judgement.

(* SEMANTICS *)
Reserved Notation "t1 '-->(' L ')' t2" (at level 48).
Inductive reducts : Level -> typedterm -> typedterm -> Prop :=
| E_App1 : forall L t1 t2 t1' T, t1 -->(L) t1' -> (App t1 t2 : T) -->(L) (App t1' t2 : T)
| E_App2 : forall L t1 t2 t2' T, t2 -->(L) t2' -> (App t1 t2 : T) -->(L) (App t1 t2' : T)
(* | E_Abs : forall t t' T1 T, *)
(*   t -->(L1) t' -> *)
(*   (Lam T1 t : T) -->(L1) (Lam T1 t' : T) *)
| E_Lift_Red : forall n TN T,
    (Lift (Nat n : TN) : T) -->(L0) (Box (Nat n : TN) : T)
| E_Lift : forall t t' T,
    t -->(L0) t' ->
    (Lift t : T) -->(L0) (Lift t' : T)
| E_Beta : forall t T1 T2 v,
    (App (Lam T1 t : (T1 ==> T2)) v : T2) -->(L0) substitute v t
where "t1 '-->(' L ')' t2" := (reducts L t1 t2).

(* PROPERTIES *)

Inductive isvalue : typedterm -> Prop :=
| Val_Nat : forall n T, isvalue (Nat n : T)
| Val_Lam : forall t T1 T, isvalue (Lam T1 t : T)
| Val_Box : forall t T, isvalue (Box t : T)
.

