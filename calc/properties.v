Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.
Require Import Coq.Bool.Bool.

Require Import syntax.
Require Import types.
Require Import semantics.

Definition dec (x y : nat) : x = y \/ x <> y.
  remember (x =? y).
  destruct b.
  * left. apply beq_nat_true. intuition.
  * right. apply beq_nat_false. intuition.
Qed.

Definition decT (x y : type) : x = y \/ x <> y.
  remember (type_beq x y).
  destruct b.
  - left. apply type_beq_iff. auto.
  - right. intro.
    apply type_beq_iff in H.
    congruence.
Qed.

(* Proofs *)

Lemma CanonicalForms1 : forall G t,
    G ⊢(L0) t ∈ TNat ->
    isvalue t ->
    exists n, t = (Nat n : TNat).
  intros.
  inversion H0; inversion H; subst; try (cbv in *; congruence).
  inversion H. subst.
  exists n. trivial.
Qed.

Lemma CanonicalForms2 : forall G t T1 T2,
    G ⊢(L0) t ∈ (T1 ==> T2) ->
    isvalue t ->
    exists t', t = (Lam T1 t' : T1 ==> T2).
  intros.
  inversion H0; inversion H; subst; try (cbv in *; congruence).
  inversion H. subst. eexists. auto.
Qed.

Lemma CanonicalForms3 : forall G t T,
    G ⊢(L0) t ∈ (□T) ->
    isvalue t ->
    exists t', isplain t' /\ t = (Quote t' : □T).
  intros.
  inversion H0; inversion H; subst; try (cbv in *; congruence).
  eexists.
  constructor.
  2 : {
    eauto.
  }
  cbn in H2. auto.
Qed.

Ltac simpl_match :=
  match goal with
  | H: context[match ?x with _ : _ => ?b end] |- _ => destruct x
  end.

Ltac crush_type_beq_if :=
  match goal with
  | H: context [if (type_beq ?T1 ?T2 && ?other) then ?A else ?B] |- _ =>
    let B := fresh "B" in
    let HB := fresh "HeqB" in
    (remember (type_beq T1 T2) as B eqn:HB; destruct B; try apply type_beq_iff in HB)
  | _ => fail "if type_beq T1 T2 && ... not found"
  end.

Ltac crush_type_beq_single :=
  match goal with
  | H: context [type_beq ?T1 ?T2] |- _ =>
    let B := fresh "B" in
    let HB := fresh "HeqB" in
    (remember (type_beq T1 T2) as B eqn:HB; destruct B; try apply type_beq_iff in HB)
  | _ => fail "type_beq T1 T2 not found"
  end.

Ltac crush_type_beq := repeat (crush_type_beq_if; simpl in *); simpl in *; try crush_type_beq_single.


(* We don't have a Correspondence Lemma anymore, as there's no Match function.
   The Pattern Match Lemma will be split into substitution lemmas for each pattern with binders, ie.
   PatAppSubstitution, PatUnliftSubstitution and PatLam substitution *)

Definition RestrictedLevel (G : TypEnv) (L : Level) : Prop := forall x L' T', lookup x G = Some (L', T') -> L' = L.


Ltac goL0 := left; constructor; trivial.
Ltac goL1 := right; constructor; trivial; intros.

Corollary IHL0 : forall G t T,
  (forall G T L,
    RestrictedLevel G L1 ->
    G ⊢(L) t ∈ T ->
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t'))) ->
  G ⊢(L0) t ∈ T ->
  RestrictedLevel G L1 ->
  (isvalue t \/ (exists t' : typedterm, t -->( L0) t')).
  intros.
  assert (L0 = L0 /\
     (isvalue t \/ (exists t' : typedterm, t -->( L0) t')) \/
     L0 = L1 /\
     (~ isvalue (Quote t : □ T) ->
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
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t'))) ->
  G ⊢(L1) t ∈ T ->
  RestrictedLevel G L1 ->
  (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t').
  intros G t T.
  intro IH.
  intros H1 H2.
  assert ((L1 = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L1 = L1 /\ (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t'))).
  - eauto using IH.
  - destruct H; destruct H.
    + discriminate.
    + trivial.
Qed.

(* Ltac goIHt0 t T := *)
(*     assert (isvalue t \/ (exists t' : typedterm, t -->( L0) t')); eapply InductiveHypL0. *)

Lemma AddingRestrictedDoesNotRemoveRestriction : forall G L T,
    RestrictedLevel G L ->
    RestrictedLevel (insert 0 (L,T) G) L.
  intros.
  unfold RestrictedLevel in *.
  intros.
  destruct x; lookup_insert_all; auto.
  eauto using H.
Qed.

Ltac autoselectL0L1Case := (match goal with
               | |- context[L0 = L0] => goL0
               | |- context[L1 = L1] => goL1
               end).

Lemma isplain_decidable t1 : (decide_isplain t1 = true) \/ (decide_isplain t1 = false).
  remember (decide_isplain t1).
  destruct b; eauto.
Qed.

Ltac crushFail Rule := eexists; (eapply Rule; eauto); congruence.
Ltac crushFails := solve [crushFail E_PatNat_Fail
                         | crushFail E_PatVar_Fail
                         | crushFail E_PatApp_Fail
                         | crushFail E_PatUnlift_Fail
                         | crushFail E_PatLam_Fail
                       ].

Ltac prepareMatchProgress :=
  match goal with
  | hval: isvalue ?t1 |- _ =>
    match goal with
    | htyp: ?G ⊢(L0) t1 ∈ □?T |- _ =>
      let Hisval := fresh "Hisval" in
      (inversion hval as [Hisval];
       (inversion htyp; subst; cbn in Hisval; try congruence);
       (match goal with
        | hl1: G ⊢(L1) ?t ∈ ?T |- _ =>
          let ter := fresh "ter" in
          let ty := fresh "T" in
          destruct t as [ter ty]; destruct ter; cbn in Hisval; try congruence;
          try crushFails
       end))
      (* (destruct t; destruct u; cbn in Hisval; try congruence; try (crushFail E_PatNat_Fail). *)
    end
  end.

Lemma LevelProgress : forall t G T L,
    RestrictedLevel G L1 ->
    G ⊢(L) t ∈ T ->
    (L = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L = L1 /\ (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t')).
  intro.
  induction t using syntactic; intros; destruct L; autoselectL0L1Case; unfold isvalue in *; try solve [cbn; intuition | inversion H0].
  - (* VAR L0 *)
    exfalso.
    unfold RestrictedLevel in H.
    inversion H0. subst.
    apply H in H6. congruence.
  - (* Lam L1 *)
    inversion H0; subst.
    eapply IHL1 in IHt; eauto.
    + inversion IHt.
      exists (Lam argT x : argT ==> T2).
      auto.
    + eauto using AddingRestrictedDoesNotRemoveRestriction.
  - (* App L0 *)
    right.
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    eapply IHL0 in IHt2; eauto.
    destruct IHt1.
    + destruct IHt2.
      * eapply CanonicalForms2 in H1; eauto.
        inversion H1. subst. eexists. eauto.
      * inversion H2. eexists; eauto.
    + inversion H1. eexists; eauto.
  - (* App L1 *)
    assert (decide_isvalue (Quote (App t1 t2 : T) : □ T0) = false) as Hv.
    auto using Bool.not_true_is_false.
    cbn in Hv. apply Bool.andb_false_iff in Hv.
    inversion H0; subst.
    destruct Hv.
    + eapply IHL1 in IHt1; eauto.
      * inversion IHt1. eexists. eauto.
      * unfold isvalue. cbn. congruence.
    + eapply IHL1 in IHt2; eauto.
      * inversion IHt2. eexists; eauto.
      * unfold isvalue. cbn. congruence.
  - (* Lift L0 *)
    inversion H0.
    eapply IHL0 in IHt; eauto. subst.
    right.
    destruct IHt.
    + inversion H4; intuition; cbv in H1; subst; try congruence.
      inversion H4. subst.
      exists (Quote (Nat n : TNat) : □TNat).
      eauto.
    + inversion H1.
      exists (Lift x : □TNat).
      auto.
  - (* Quote L0 *)
    remember (decide_isvalue (Quote t : T)) as QtV.
    destruct QtV.
    + left. trivial.
    + right. inversion H0; subst.
      eapply IHL1 in IHt; eauto.
      inversion IHt.
      exists (Quote x : □ T1). eauto.
      unfold isvalue. congruence.
  - (* Splice L1 *)
    inversion H0. subst.
    eapply IHL0 in IHt; eauto.
    destruct IHt.
    + eapply CanonicalForms3 in H2; eauto.
      inversion H2.
      destruct H3. subst.
      eexists. eauto.
    + inversion H2. eexists. eauto.
  - right. (* MatchNat *)
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    destruct IHt1.
    + prepareMatchProgress.
      destruct (dec n0 n); subst; try (crushFail E_PatNat_Fail).
      eexists. eapply E_PatNat_Succ; eauto.
      inversion H0. subst. inversion H4. auto.
    + inversion H1.
      eexists.
      eapply E_PatNat_Red. eauto.
  - right. (* MatchVar *)
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    destruct IHt1.
    + prepareMatchProgress.
      destruct (dec x x0); subst.
      * eexists. eapply E_PatVar_Succ; eauto.
        inversion H4; subst; auto.
      * crushFails.
    + inversion H1. eexists. eapply E_PatVar_Red; eauto.
  - right. (* MatchApp *)
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    destruct IHt1.
    + prepareMatchProgress.
      inversion H4; subst.
      destruct (decT T1 T2).
      * subst.
        destruct e1; destruct e2.
        inversion H13; inversion H9; subst;
          eexists; eapply E_PatApp_Succ; eauto.
      * inversion H9; inversion H13; subst; crushFails.
    + inversion H1. eexists. eapply E_PatApp_Red; eauto.
  - right. (* MatchUnlift *)
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    destruct IHt1.
    + prepareMatchProgress.
      eexists. eapply E_PatUnlift_Succ; eauto.
      inversion H4. eauto.
    + inversion H1. eexists. eapply E_PatUnlift_Red; eauto.
  - right. (* MatchLam *)
    inversion H0; subst.
    eapply IHL0 in IHt1; eauto.
    destruct IHt1.
    + prepareMatchProgress.
      eexists. eapply E_PatLam_Succ; eauto.
      inversion H4. eauto.
    + inversion H1. eexists. eapply E_PatLam_Red; eauto.
Qed.

Lemma LevelProgress0 : forall G t T,
    G ⊢(L0) t ∈ T ->
    RestrictedLevel G L1 ->
    isvalue t \/ exists t', t -->(L0) t'.
  intros.
  enough ((L0 = L0 /\ (isvalue t \/ exists t', t -->(L0) t')) \/ (L0 = L1 /\ (not (isvalue (Quote t : □T)) -> exists t', t -->(L1) t'))).
  - destruct H1; intuition.
    + congruence.
  - eapply LevelProgress; eauto.
Qed.
(* with LevelProgress1 : forall G t T, *)
(*     RestrictedLevel G L1 -> *)
(*     G ⊢(L1) t ∈ T -> *)
(*     not (isvalue (Quote t : □T)) -> *)
(*     exists t', t -->(L1) t'. *)

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
  - admit.
  - admit.
Admitted.

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
  - (* PatternMatch *)
    admit.
Admitted.

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

Ltac invPM :=
  match goal with
  | H: ?G ⊢(L0) (PatternMatch ?t1 ?p ?t2 ?t3 : ?T) ∈ ?T' |- _ => inversion H; subst
  end.
(*
H10 : G ⊢p PNatLit n ∈ T1 ~~> Gp
 *)
Ltac invPP :=
  match goal with
  | H: ?G ⊢p ?p ∈ ?T ~~> ?Gp |- _ => inversion H; subst
  end.

Ltac invV :=
  match goal with
  | H: ?G ⊢(L0) ?v ∈ □(?T) |- _ => inversion H; subst
  end.

Ltac cbnMatch :=
  match goal with
  | H: Match ?t ?p = ?res |- _ => cbn in H
  end.

Lemma PatternMatching : forall p G v t2 t3 T T' σ,
    isvalue (Quote v : T') ->
    G ⊢(L0) (PatternMatch (Quote v : T') p t2 t3 : T) ∈ T ->
    Match v p = Some σ ->
    G ⊢(L0) σ t2 ∈ T.
  destruct p; intros; invPM; invPP; invV; subst; cbnMatch; try congruence; subst; repeat simpl_match; try congruence.
  - destruct v; destruct u; destruct t; try congruence; repeat simpl_match; try congruence.
    destruct (Nat.eq_dec n0 n).
    inversion H1. auto.
    congruence.
  - destruct v; destruct u; try congruence; repeat simpl_match; try congruence.
    + destruct t; try congruence.
    +
      destruct (Nat.eq_dec x0 x).
      auto.
      inversion H1.
      auto.
      congruence.
    + destruct t; try congruence.
  - destruct v; destruct u; try crush_type_beq; inversion H1; subst; try congruence; try (destruct t; repeat simpl_match; congruence).
    admit.
  - destruct v; destruct u; try crush_type_beq; inversion H1; subst; try congruence; try (destruct t; repeat simpl_match; congruence).
    destruct t; try congruence.
    inversion H1. subst.
    admit.
  - destruct v; destruct u; try crush_type_beq; inversion H1; subst; try congruence; try (destruct t; repeat simpl_match; congruence).
    destruct t; try congruence.
    crush_type_beq; crush_type_beq; crush_type_beq; try congruence.
    inversion H3; subst.
    admit.
Admitted.

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
    + apply T_Unbox. apply IHtyping_judgement. trivial.
    + inversion H; subst. auto.
  - (* Pattern Match *)
    inversion H3; subst; eauto with *.
    eapply PatternMatching; eauto.
Qed.