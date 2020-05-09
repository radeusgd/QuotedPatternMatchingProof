Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Coq.Bool.Bool.
(* SYNTAX *)

Definition DeBruijnIndex := nat.

Inductive type :=
| TNat
| TArr (T1 : type) (T2 : type)
| TBox (T : type).
Notation "'□' T" := (TBox T) (at level 48).
Notation "T1 '==>' T2" := (TArr T1 T2) (at level 48).
Scheme Equality for type.
Lemma type_beq_iff : forall T1 T2, true = type_beq T1 T2 <-> T1 = T2.
  induction T1; intros; intuition; cbn in *; destruct T2; try congruence.
  - apply andb_true_eq in H.
    destruct H. apply IHT1_1 in H. apply IHT1_2 in H0. subst. auto.
  - inversion H. subst.
    symmetry.
    apply andb_true_iff.
    constructor; symmetry.
    + eapply IHT1_1. auto.
    + eapply IHT1_2. auto.
  - apply IHT1 in H. congruence.
  - apply IHT1. congruence.
Qed.

Inductive typedterm :=
| TypedTerm (u: term) (t: type)
with term :=
     | Nat (n : nat)
     | VAR (x : DeBruijnIndex)
     | Lam (argT: type) (ebody : typedterm)
     | App (e1 e2 : typedterm)
     | Fix (e : typedterm)
     | Lift (e: typedterm)
     | Quote (e : typedterm)
     | Splice (e : typedterm)
     | MatchNat (e : typedterm) (n : nat) (es ef : typedterm)
     | MatchVar (e : typedterm) (x : term) (es ef : typedterm) (* var is a general term here but only VAR x is allowed in this term, this is done to correctly handle shifting of the DeBruijn index *)
     | MatchApp (e : typedterm) (T1 T2 : type) (es ef : typedterm) (* T1 is type of the function and T2 is type of it's argument, so if you want to deconstruct an application of the form (f 2) you should set T1 = TNat -> ?T and T2 = ?T, this may be a little counterintuitive but it is made in such a way to reflect the original calculus where you would use the app pattern nested with a bind, like so: PatApp (PatBind[TNat -> ?T] f) (PatBind[TNat] arg) *)
     | MatchUnlift (e : typedterm) (es ef : typedterm)
     | MatchLam (e : typedterm) (T : type) (es ef : typedterm)
     | MatchFix (e : typedterm) (T : type) (es ef : typedterm)
.

(* Definition RemoveType (tt : typedterm) : term := match tt with *)
(*                                                  | TypedTerm t _ => t *)
(*                                                  end. *)

(* TODO resolve this name conflict in a better way *)
Instance var_term : Var term := {
                                 var := VAR
                               }.

Fixpoint traverse_typedterm (f : nat -> nat -> term) l t :=
  match t with
  | TypedTerm u T => TypedTerm (traverse_term f l u) T
  end
with traverse_term f l u :=
       match u with
       | Nat n => Nat n
       | VAR x => f l x
       | Lam argT ebody => Lam argT (traverse_typedterm f (1 + l) ebody)
       | App e1 e2 => App (traverse_typedterm f l e1) (traverse_typedterm f l e2)
       | Fix e => Fix (traverse_typedterm f l e)
       | Lift e => Lift (traverse_typedterm f l e)
       | Quote e => Quote (traverse_typedterm f l e)
       | Splice e => Splice (traverse_typedterm f l e)
       | MatchNat e n es ef =>
         MatchNat (traverse_typedterm f l e) n (traverse_typedterm f (l) es) (traverse_typedterm f l ef)
       | MatchVar e x es ef =>
         MatchVar (traverse_typedterm f l e) (traverse_term f l x) (traverse_typedterm f (l) es) (traverse_typedterm f l ef)
       | MatchApp e T1 T2 es ef =>
         MatchApp (traverse_typedterm f l e) T1 T2 (traverse_typedterm f (2 + l) es) (traverse_typedterm f l ef)
       | MatchUnlift e es ef =>
         MatchUnlift (traverse_typedterm f l e) (traverse_typedterm f (1 + l) es) (traverse_typedterm f l ef)
       | MatchLam e T1 es ef =>
         MatchLam (traverse_typedterm f l e) T1 (traverse_typedterm f (1 + l) es) (traverse_typedterm f l ef)
       | MatchFix e T1 es ef =>
         MatchFix (traverse_typedterm f l e) T1 (traverse_typedterm f (1 + l) es) (traverse_typedterm f l ef)
       end.

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
  (* for some reason after adding the 4th recursive argument in MatchVar the automatic proof no longer manages to finish up, so some manual finish is required; unfortunately the automatic tactic also takes a lot of time because of that (expect up to a minute) *)
  fold traverse_typedterm.
  assert ((traverse_typedterm f (l + p) e) = (traverse_typedterm g l e)). eauto.
  assert ((traverse_typedterm f (l + p) es) = (traverse_typedterm g l es)). eauto.
  assert ((traverse_typedterm f (l + p) ef) = (traverse_typedterm g l ef)). eauto.
  assert ((traverse_term f (l + p) t) = (traverse_term g l t)). eauto.
  congruence.
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


Notation "u ':' T" := (TypedTerm u T) (at level 49).

Scheme typedterm_mutualind := Induction for typedterm Sort Prop
  with term_mutualind := Induction for term Sort Prop.

Lemma syntactic :
  forall (P : typedterm -> Prop),
    (forall n : nat, forall T : type, P (Nat n : T)) ->
    (forall x : DeBruijnIndex, forall T : type, P (VAR x : T)) ->
    (forall (argT : type) (ebody : typedterm), P ebody -> forall T : type, P (Lam argT ebody : T)) ->
    (forall e1 : typedterm, P e1 -> forall e2 : typedterm, P e2 -> forall T : type, P (App e1 e2 : T)) ->
    (forall e : typedterm, P e -> forall T : type, P (Fix e : T)) ->
    (forall e : typedterm, P e -> forall T : type, P (Lift e : T)) ->
    (forall e : typedterm, P e -> forall T : type, P (Quote e : T)) ->
    (forall e : typedterm, P e -> forall T : type, P (Splice e : T)) ->
    (forall (e s f : typedterm) (n : nat), P e -> P s -> P f -> forall T : type, P (MatchNat e n s f : T)) ->
    (forall (e s f : typedterm) (x : term), P e -> P s -> P f -> forall T : type, P (MatchVar e x s f : T)) -> (* not sure if P x should be included? *)
    (forall (e s f : typedterm) (T1 T2 : type), P e -> P s -> P f -> forall T : type, P (MatchApp e T1 T2 s f : T)) ->
    (forall (e s f : typedterm), P e -> P s -> P f -> forall T : type, P (MatchUnlift e s f : T)) ->
    (forall (e s f : typedterm) (T1 : type), P e -> P s -> P f -> forall T : type, P (MatchLam e T1 s f : T)) ->
    (forall (e s f : typedterm) (T1 : type), P e -> P s -> P f -> forall T : type, P (MatchFix e T1 s f : T)) ->

    forall t : typedterm, P t
.
  intros.
  eapply typedterm_mutualind.
  - intro. intro Hp. exact Hp.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
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
Notation "t1 .[ t2 /]" := (substitute t2 t1) (at level 45).
Lemma fold_subst : forall u t T, (substitute (u : T) t) = subst u 0 t.
  intros.
  auto.
Qed.
