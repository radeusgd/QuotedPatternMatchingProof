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
     | Quote (e : typedterm)
     | Splice (e : typedterm)
(* | PatternMatch (e : typedterm) (pat : pattrn) (success failure : typedterm) *)
.
Notation "u ':' T" := (TypedTerm u T) (at level 49).
Scheme typedterm_mutualind := Induction for typedterm Sort Prop
  with term_mutualind := Induction for term Sort Prop.
Check typedterm_mutualind.
Lemma syntactic :
  forall (P : typedterm -> Prop),
    (forall n : nat, forall T : type, P (Nat n : T)) ->
    (forall x : DeBruijnIndex, forall T : type, P (VAR x : T)) ->
    (forall (argT : type)
       (ebody : typedterm),
        P ebody -> forall T : type, P (Lam argT ebody : T)) ->
    (forall e1 : typedterm,
        P e1 ->
        forall e2 : typedterm,
          P e2 -> forall T : type, P (App e1 e2 : T)) ->
    (forall e : typedterm,
        P e -> forall T : type, P (Lift e : T)) ->
    (forall e : typedterm,
        P e -> forall T : type, P (Quote e : T)) ->
    (forall e : typedterm,
        P e -> forall T : type, P (Splice e : T)) ->
    forall t : typedterm, P t
.
  intros.
  eapply typedterm_mutualind.
  - intro. intro.
    exact H6.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - auto.
Qed.

(* Definition RemoveType (tt : typedterm) : term := match tt with *)
(*                                                  | TypedTerm t _ => t *)
(*                                                  end. *)

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
       | Quote e => Quote (traverse_typedterm f l e)
       | Splice e => Splice (traverse_typedterm f l e)
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
Notation "t1 .[ t2 /]" := (substitute t2 t1) (at level 45).
Lemma fold_subst : forall u t T, (substitute (u : T) t) = subst u 0 t.
  intros.
  auto.
Qed.

(* TYPES *)

Require Import Dblib.Environments.
Inductive Level := L0 | L1.
Definition TypEnv := env (Level * type).
Definition emptyEnv : env (Level * type) := empty (Level * type).
Notation "∅" := emptyEnv.
(* Notation "'extendEnv' G L T" := (insert 0 (L, T) G) (at level 49). *)
(* Definition extendEnv (G : TypEnv) (L : Level) (T : type) : TypEnv := (insert 0 (L, T) G). *)
(* Hint Unfold extendEnv. *)
(* Notation "G ';' L T" := (insert 0 (L, T) G) (at level 49). *)

(* Definition env_has (G : TypEnv) (x : DeBruijnIndex) (L : Level) (T : type) : Prop := *)
  (* lookup x G = Some (L, T). *)

Reserved Notation "G '⊢(' L ')' t '∈' T" (at level 40, t at level 59, T at level 59).
Inductive typing_judgement : TypEnv -> Level -> typedterm -> type -> Prop :=
| T_Nat : forall L G n, G ⊢(L) (Nat n : TNat) ∈ TNat
| T_Var : forall L G x T,
    lookup x G = Some (L, T) ->
    G ⊢(L) (VAR x : T) ∈ T
| T_Abs : forall L G T1 T2 body,
    insert 0 (L, T1) G ⊢(L) body ∈ T2 ->
    G ⊢(L) (Lam T1 body : T1 ==> T2) ∈ (T1 ==> T2)
| T_App : forall L G T1 T2 t1 t2,
    G ⊢(L) t1 ∈ (T1 ==> T2) ->
    G ⊢(L) t2 ∈ T1 ->
    G ⊢(L) (App t1 t2: T2) ∈ T2
| T_Lift : forall G t,
    G ⊢(L0) t ∈ TNat ->
    G ⊢(L0) (Lift t : ⧈TNat) ∈ ⧈TNat
| T_Box : forall G t T,
    G ⊢(L1) t ∈ T ->
    G ⊢(L0) (Quote t : ⧈T) ∈ ⧈T
| T_Unbox : forall G t T,
    G ⊢(L0) t ∈ ⧈T ->
    G ⊢(L1) (Splice t : T) ∈ T
(* | T_Fix : TODO *)
(* | T_Pat : TODO *)
where "G '⊢(' L ')' t '∈' T" := (typing_judgement G L t T).
Hint Constructors typing_judgement.

(* SEMANTICS *)
Reserved Notation "t1 '-->(' L ')' t2" (at level 48).
Inductive reducts : Level -> typedterm -> typedterm -> Prop :=
| E_App1 : forall L t1 t2 t1' T, t1 -->(L) t1' -> (App t1 t2 : T) -->(L) (App t1' t2 : T)
| E_App2 : forall L t1 t2 t2' T, t2 -->(L) t2' -> (App t1 t2 : T) -->(L) (App t1 t2' : T)
| E_Abs : forall t t' T1 T,
  t -->(L1) t' ->
  (Lam T1 t : T) -->(L1) (Lam T1 t' : T)
| E_Box : forall t t' T,
    t -->(L1) t' ->
    (Quote t : T) -->(L0) (Quote t' : T)
| E_Unbox : forall t t' T,
    t -->(L0) t' ->
    (Splice t : T) -->(L1) (Splice t' : T)
| E_Lift_Red : forall n TN T,
    (Lift (Nat n : TN) : T) -->(L0) (Quote (Nat n : TN) : T)
| E_Lift : forall t t' T,
    t -->(L0) t' ->
    (Lift t : T) -->(L0) (Lift t' : T)
| E_Beta : forall t T1 T2 v,
    (App (Lam T1 t : (T1 ==> T2)) v : T2) -->(L0) t.[v/]
(* | E_Fix : TODO *)
(* | E_Fix_Red : TODO *)
(* | E_Pat : TODO *)
(* | E_Pat_Succ : TODO *)
(* | E_Pat_Fail : TODO *)
where "t1 '-->(' L ')' t2" := (reducts L t1 t2).
Hint Constructors reducts.

(* PROPERTIES *)
Inductive isplain : typedterm -> Prop :=
| Plain_tt : forall t T, isplaint t -> isplain (t : T)
with
isplaint : term -> Prop :=
| Plain_nat : forall n, isplaint (Nat n)
| Plain_var : forall x, isplaint (VAR x)
| Plain_lam : forall T t, isplain t -> isplaint (Lam T t)
| Plain_app : forall t1 t2, isplain t1 -> isplain t2 -> isplaint (App t1 t2)
(* | Plain_fix : TODO *)
.
Hint Constructors isplain.
Hint Constructors isplaint.

Fixpoint decide_isplain (t : typedterm) : bool :=
  match t with
  | TypedTerm t' _ =>
    match t' with
    | Nat _ => true
    | VAR _ => true
    | Lam _ ebody => decide_isplain ebody
    | App e1 e2 => (decide_isplain e1) && (decide_isplain e2)
    | _ => false
    end
  end.

Hint Immediate Bool.andb_true_iff.

Lemma isplain_decidable (t : typedterm) :
  decide_isplain t = true <-> isplain t.
  induction t using syntactic; intuition; eauto; try solve [inversion H0 | inversion H1; inversion H3].
  - cbn. inversion H1. inversion H3. subst. auto.
  - inversion H3.
    apply Bool.andb_true_iff in H5.
    intuition.
  - cbn. inversion H3. inversion H5. subst. intuition.
Qed.

Lemma isplain_decidable2 (t : typedterm) :
  {isplain t} + {~ isplain t}.
  remember (decide_isplain t) as ipt.
  destruct ipt.
  left.
  apply isplain_decidable. auto.
  right. intro.
  apply isplain_decidable in H. congruence.
Qed.

Inductive isvalue : typedterm -> Prop :=
| Val_Nat : forall n T, isvalue (Nat n : T)
| Val_Lam : forall t T1 T, isvalue (Lam T1 t : T)
| Val_Box : forall t T, isplain t -> isvalue (Quote t : T)
.
Hint Constructors isvalue.

Fixpoint decide_isvalue (t : typedterm) : bool :=
  match t with
  | TypedTerm t' _ =>
    match t' with
    | Nat _ => true
    | Lam _ ebody => true
    | Quote t => decide_isplain t
    | _ => false
    end
  end.

Lemma isvalue_decidable (t : typedterm) : isvalue t <-> decide_isvalue t = true.
  induction t using syntactic; intuition; try (inversion H); try inversion H1.
  - inversion H3.
  - cbv in H3. congruence.
  - subst. cbn.
    apply isplain_decidable. auto.
  - constructor. apply isplain_decidable. auto.
Qed.

Lemma isvalue_decidable2 (t : typedterm) : {isvalue t} + {~ isvalue t}.
  remember (decide_isvalue t) as ivt.
  destruct ivt.
  left.
  apply isvalue_decidable. auto.
  right.
  intro.
  apply isvalue_decidable in H. congruence.
Qed.

Definition id_nat := (Lam TNat (VAR 0 : TNat) : TNat ==> TNat).
Lemma test_red : (App id_nat (Nat 42 : TNat) : TNat) -->(L0) (Nat 42 : TNat).
  apply E_Beta.
Qed.

Lemma CanonicalForms1 : forall G t,
    G ⊢(L0) t ∈ TNat ->
    isvalue t ->
    exists n, t = (Nat n : TNat).
  intros.
  inversion H0; inversion H; subst; try congruence.
  inversion H.
  exists n. trivial.
Qed.

Lemma CanonicalForms2 : forall G t T1 T2,
    G ⊢(L0) t ∈ (T1 ==> T2) ->
    isvalue t ->
    exists t', t = (Lam T1 t' : T1 ==> T2).
  intros.
  inversion H0; inversion H; subst; try congruence.
  inversion H5. subst. eexists. auto.
Qed.

Lemma CanonicalForms3 : forall G t T,
    G ⊢(L0) t ∈ (⧈T) ->
    isvalue t ->
    exists t', isplain t' /\ t = (Quote t' : ⧈T).
  intros.
  inversion H0; inversion H; subst; try congruence.
  eexists.
  constructor.
  exact H1.
  congruence.
Qed.

Definition RestrictedLevel (G : TypEnv) (L : Level) : Prop := forall x L' T', lookup x G = Some (L', T') -> L' = L.


Ltac goL0 := left; constructor; trivial.
Ltac goL1 := right; constructor; trivial; intros.

Corollary IHL0 : forall G t T,
  (forall G T L,
    RestrictedLevel G L1 ->
    G ⊢(L) t ∈ T ->
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t'))) ->
  RestrictedLevel G L1 ->
  G ⊢(L0) t ∈ T ->
  (isvalue t \/ (exists t' : typedterm, t -->( L0) t')).
  intros.
  assert (L0 = L0 /\
     (isvalue t \/ (exists t' : typedterm, t -->( L0) t')) \/
     L0 = L1 /\
     (~ isvalue (Quote t : ⧈ T) ->
      exists t' : typedterm, t -->( L1) t')).
  - eapply H; eauto.
  - destruct H2; destruct H2.
    + trivial.
    + discriminate.
Qed.

Corollary IHL1 : forall G t T,
  (forall G T L,
    RestrictedLevel G L1 ->
    G ⊢(L) t ∈ T ->
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t'))) ->
  RestrictedLevel G L1 ->
  G ⊢(L1) t ∈ T ->
  (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t').
  intros G t T.
  intro IH.
  intros H1 H2.
  assert ((L1 = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L1 = L1 /\ (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t'))).
  - eauto using IH.
  - destruct H; destruct H.
    + discriminate.
    + trivial.
Qed.

(* Ltac goIHt0 t T := *)
(*     assert (isvalue t \/ (exists t' : typedterm, t -->( L0) t')); eapply InductiveHypL0. *)


Lemma LevelProgress : forall t G T L,
    RestrictedLevel G L1 ->
    G ⊢(L) t ∈ T ->
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t')).
  intro.
  induction t using syntactic; intros; destruct L; try solve [intuition].
  - goL1.
    enough (isvalue (Quote (Nat n : T) : ⧈T0)).
    congruence.
    eauto.
  - goL0.
    exfalso.
    unfold RestrictedLevel in H.
    inversion H0. subst.
    apply H in H6. congruence.
  - goL1.
    exfalso.
    apply H1.
    eauto.
  - goL1.
    destruct (isvalue_decidable2 t).
    + admit.
    + admit.
  - goL0.
    admit.
  - goL1. admit.
  - goL0.
    inversion H0.
    eapply IHL0 in IHt; eauto. subst.
    right.
    destruct IHt.
    + inversion H1; inversion H4; intuition; try congruence.
      subst.
      inversion H4. subst.
      exists (Quote (Nat n : TNat) : ⧈TNat). auto.
    + inversion H1.
      exists (Lift x : ⧈TNat).
      auto.
  - inversion H0.
  - 

    (* remember (decide_isplain t) as IsPlainT. *)
    (* destruct IsPlainT. *)
    (* + assert (isplain t). *)
    (*   unfold isplain. auto. *)
    (*   exfalso. apply H1. auto. *)
    (* + *)
    (*   inversion H0; subst. *)
    (*   assert (L1 = L0 /\ *)
    (*     (isvalue t \/ (exists t' : typedterm, t -->( L0) t')) \/ *)
    (*     L1 = L1 /\ *)
    (*     (~ isvalue (Quote t : ⧈ T2) -> *)
    (*      exists t' : typedterm, t -->( L1) t')). *)
    (*   eapply IHt. *)
    (*   2: { *)
    (*     eauto. *)
    (*   } *)
    (*   * unfold RestrictedLevel. *)
    (*     intros. *)
    (*     destruct x. *)
    (*     lookup_insert_all. auto. *)
    (*     lookup_insert_all. eapply H. eauto. *)
    (*   * destruct H2. *)
    (*     ** destruct H2. congruence. *)
    (*     ** *)
    (*       assert (~ isvalue (Quote t : ⧈ T2) -> *)
    (*               exists t' : typedterm, t -->( L1) t'). *)
    (*       intuition. *)
          

    

Admitted.

Lemma LevelProgress0 : forall G t T,
    G ⊢(L0) t ∈ T ->
    RestrictedLevel G L1 ->
    isvalue t \/ exists t', t -->(L0) t'.
  intros.
  enough ((L0 = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L0 = L1 /\ (not (isvalue (Quote t : ⧈T)) -> exists t', t -->(L1) t'))).
  - destruct H1; intuition.
    + congruence.
  - eapply LevelProgress; eauto.
Qed.
(* with LevelProgress1 : forall G t T, *)
(*     RestrictedLevel G L1 -> *)
(*     G ⊢(L1) t ∈ T -> *)
(*     not (isvalue (Quote t : ⧈T)) -> *)
(*     exists t', t -->(L1) t'. *)
(*   - intros. eapply typedterm_mutualind. admit. *)
(* Admitted. *)
Theorem Progress : forall t T,
    ∅ ⊢(L0) t ∈ T ->
    isvalue t \/ exists t', t -->(L0) t'.
  intros.
  eapply LevelProgress0. eauto.
  unfold RestrictedLevel.
  intros.
  exfalso.
  eapply lookup_empty_Some. eauto.
Qed.

Ltac sub :=
  (* unfold substitute; *)
  (match goal with
         | |- context[substitute ?t _] => destruct t
         (* | h: context[substitute ?t _] |- _ => destruct t *)
  end; unfold substitute; simpl_subst_all).
  (* repeat match goal with *)
  (*        | [ t : typedterm |- _ ] => *)
  (*          destruct t *)
  (*        end; unfold substitute; simpl_subst_all. *)

Ltac fold_sub := repeat erewrite <- fold_subst.
  (* ((assert (subst u 0 t = substitute (u : T) t) as Happ); *)
  (* eapply fold_subst; rewrite Happ; destruct Happ). *)

Compute (shift 0 (VAR 1 : TNat)).
Compute (subst (Nat 42) 1 (VAR 0 : TNat)).

Lemma AscribedTypeIsCorrect : forall G L t T T',
    G ⊢(L) (t : T) ∈ T' -> T = T'.
  intros.
  inversion H; auto.
Qed.

(* Based on https://github.com/coq-community/dblib/blob/master/src/DemoLambda.v *)

Lemma Weakening: forall G L t T,
  G ⊢(L) t ∈ T ->
  forall x L' T' G',
  insert x (L', T') G = G' ->
  G' ⊢(L) (shift x t) ∈ T.
  induction 1; intros; subst; simpl_lift_goal;
    econstructor; eauto with lookup_insert insert_insert.
Qed.

Lemma Substitution : forall t2 G x Lo Li T1 T2,
  (insert x (Li, T1) G) ⊢(Lo) t2 ∈ T2 ->
  forall t1,
  G ⊢(Li) (t1 : T1) ∈ T1 ->
  G ⊢(Lo) (subst t1 x t2) ∈ T2.
  induction t2 using syntactic; intros; inversion H; subst; try (simpl_subst_all; eauto).
  - unfold subst_idx; dblib_by_cases; lookup_insert_all; eauto.
    intro. subst. trivial.
  - econstructor.
    eapply IHt2.
    + enough (insert (1 + x) (Li, T1) (insert 0 (Lo, argT) G) = insert 0 (Lo, argT) (insert x (Li, T1) G)).
      rewrite H1. trivial.
      insert_insert.
    + enough ((shift 0 (t1 : T1)) = (shift 0 t1) : T1).
      rewrite <- H1.
      eapply Weakening.
      eauto.
      eauto.
      eauto.
Qed.

Lemma SubstitutionSimple : forall t2 Li Lj G t1 T1 T2,
    G ⊢(Lj) t1 ∈ T1 ->
    (insert 0 (Lj, T1) G) ⊢(Li) t2 ∈ T2 ->
    (* special care will have to be taken here with patterns *)
    G ⊢(Li) t2.[t1/] ∈ T2.
  intros.
  sub.
  eapply Substitution; eauto.
  remember H as H2. clear HeqH2.
  apply AscribedTypeIsCorrect in H.
  subst.
  trivial.
Qed.

Theorem Preservation : forall t1 T G L,
    G ⊢(L) t1 ∈ T ->
    forall t2,
    t1 -->(L) t2 ->
    G ⊢(L) t2 ∈ T.
  intros until L.
  intro.
  induction H; intros.
  - inversion H.
  - inversion H0.
  - inversion H0. subst.
    assert (insert 0 (L1, T1) G ⊢( L1) t' ∈ T2).
    apply IHtyping_judgement. trivial.
    apply T_Abs. trivial.
  - inversion H1; subst; try (eapply T_App; eauto).
    eapply SubstitutionSimple. eauto.
    inversion H. auto.
  - inversion H0; subst.
    + inversion H; subst. apply T_Box. auto.
    + apply T_Lift. apply IHtyping_judgement. easy.
  - inversion H0; subst. eapply T_Box.
    apply IHtyping_judgement. easy.
  - inversion H0; subst.
    apply T_Unbox. apply IHtyping_judgement. trivial.
Qed.
