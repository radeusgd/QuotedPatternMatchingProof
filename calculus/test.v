Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.
Require Import Coq.Bool.Bool.

Require Import syntax.
Require Import types.
Require Import semantics.

(* simple 'Unit tests' *)
Definition id_nat := (Lam TNat (VAR 0 : TNat) : TNat ==> TNat).
Definition id_applied := (App id_nat (Nat 42 : TNat) : TNat).
Lemma id_app_types : ∅ ⊢(L0) id_applied ∈ TNat.
  repeat econstructor.
Qed.
Lemma id_app_evals : evaluates id_applied (Nat 42 : TNat).
  eapply star_step. repeat econstructor.
  unfold substitute. simpl_subst_all.
  auto.
Qed.

Definition const (n : nat):= (Nat n : TNat).
Definition box_const (n : nat) := (Quote (const n) : □TNat).
Hint Unfold const box_const.

Lemma SpliceTest : evaluates
                 (Quote (Splice (Quote (const 42) : □TNat) : TNat) : □TNat)
                 (Quote (const 42) : □TNat).
  eapply star_step.
  repeat econstructor.
  eapply star_refl.
Qed.

Definition UnliftConstant := (MatchUnlift (Quote (const 42) : □TNat) (VAR 0 : TNat) (const 1) : TNat).
Lemma UnliftConstantTypechecks : ∅ ⊢(L0) UnliftConstant ∈ TNat.
  cbv.
  econstructor; eauto.
Qed.
Lemma UnliftConstantEvaluates : UnliftConstant -->(L0) (const 42).
  cbv.
  econstructor; cbv; eauto.
Qed.

Lemma UnliftConstantWrongEvaluationNotPossible : ~(UnliftConstant -->(L0) (const 1)).
  intro.
  cbv in *.
  inversion H.
  subst.
  inversion H7. simpl_subst_all. subst.
  inversion H4.
  subst. inversion H4. subst.
  eapply H6.
  eauto.
Qed.

Lemma UnliftNotNatFails : (MatchUnlift (Quote (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) : □(TNat ==> TNat)) (VAR 0 : TNat) (const 1) : TNat) -->(L0) (const 1).
  eapply E_PatUnlift_Fail; eauto.
  - cbv. auto.
  - intro. congruence.
Qed.

Definition PMatchNat v := (MatchNat (v) 42 (const 23) (const 1) : TNat).

Lemma MatchNatTypes : forall G, G ⊢(L0) PMatchNat (box_const 0) ∈ TNat.
  intro.
  repeat econstructor.
Qed.

Lemma MatchNatSucc : evaluates (PMatchNat (box_const 42)) (const 23).
  econstructor; cbv.
  econstructor; cbv; eauto.
  eauto.
Qed.

Hint Unfold isplain.

Lemma MatchNatFail : evaluates (PMatchNat (box_const 123)) (const 1).
  econstructor; cbv.
  eapply E_PatNat_Fail; eauto.
  congruence.
  eauto.
Qed.

Lemma MatchNatNotSucc : ~ (evaluates (PMatchNat (box_const 42)) (const 1)).
  intro.
  inversion H; subst.
  inversion H0; subst.
  cbv in *.
  inversion H1; subst.
  inversion H2.
  inversion H8; subst.
  inversion H4; subst.
  inversion H8; subst.
  eapply H10. eauto.
Qed.

Lemma MatchNatNotFail : ~ (evaluates (PMatchNat (box_const 123)) (const 23)).
  intro.
  inversion H; subst.
  inversion H0; subst.
  cbv in *.
  inversion H8.
  inversion H8; subst.
  inversion H4; subst.
  inversion H1; subst.
  inversion H2.
Qed.

(* more complex test - reverse order of arguments if the matching function is fst *)
(*
rev :: □Nat -> □Nat
let rev code = code ~ (g y) ?
                             g ~ (f x) ?
                             f ~ fst ?
                             □{$f $y $x}
                              || code
                              || code
                              || code
in
rev □{fst 1 2} --> □{fst 2 1}
or
rev □{snd 1 2} --> □{snd 1 2}

translate refl to DeBruijn
assume context:
□{ (λfst:?. λsnd:?. ${[refl] [code]}) [fst] [snd] }
rev =
λ(□TNat).
  #0 ~ PApp (Nat -> Nat) (Nat) ?
  // fst :: snd :: code :: g :: y
  (#1 ~ PApp (Nat -> (Nat -> Nat)) (Nat) ?
  // fst :: snd :: code :: g :: y :: f :: x
  (#1 ~ #6 ?
  // fst :: snd :: code :: g :: y :: f :: x
  □{ ($#1 $#2) $#0}
  || #4)
  || #2)
  || #0
 *)

Definition funtype := (TNat ==> (TNat ==> TNat)).
Definition fun_fst := (Lam TNat (Lam TNat (VAR 1 : TNat) : TNat ==> TNat) : TNat ==> (TNat ==> TNat)).
Definition fun_snd := (Lam TNat (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) : TNat ==> (TNat ==> TNat)).
Definition code_fst := App (App (VAR 1 : funtype) (const 1) : TNat ==> TNat) (const 2) : TNat.
Definition code_snd := App (App (VAR 0 : funtype) (const 1) : TNat ==> TNat) (const 2) : TNat.
Definition rev :=
  (Lam (□TNat) (
         (MatchApp (VAR 0 : □TNat)
                       (TNat ==> TNat) TNat
                       (MatchApp (VAR 1 : □(TNat ==> TNat))
                                     funtype TNat
                                     (MatchVar (VAR 1 : □(TNat ==> (TNat ==> TNat)))
                                                   (VAR 6)
                                                   (Quote
                                                      (App
                                                         (App
                                                            (Splice (VAR 1 : □funtype) : TNat ==> (TNat ==> TNat))
                                                            (Splice (VAR 2 : □TNat) : TNat)
                                                          : TNat ==> TNat)
                                                         (Splice (VAR 0 : □TNat) : TNat)
                                                      : TNat)
                                                    : □TNat)
                                                   (VAR 4 : □TNat)
                                      : □TNat)
                                     (VAR 2 : □TNat)
                        : □TNat)
                       (VAR 0 : □TNat)
          : □TNat)

       ) : □TNat ==> □TNat).

Definition in_ctx (code : typedterm) :=
  Quote (App
           (App
              (Lam (funtype)
                   (Lam (funtype)
                        (code)
                    : funtype ==> TNat)
               : funtype ==> (funtype ==> TNat))
              fun_fst
            : funtype ==> TNat)
           fun_snd
         : TNat) : □TNat
.
Definition run_in_ctx (code : typedterm) := in_ctx (Splice code : TNat).

(*
for starters we will execute in this context
${ [fst_box] [□0] [□1] }
which should result in a value 0 wrapped in the context
(we place a level 0 fst in-place, don't use the level 1 from the context, the context is there just for the purpose of simulation)
 *)

Definition fst_box := (Lam (□TNat) (Lam (□TNat) (VAR 1 : □TNat) : □TNat ==> □TNat) : □TNat ==> (□TNat ==> □TNat)).
Definition first_box := App (App fst_box (box_const 0) : □TNat ==> □TNat) (box_const 1) : □TNat.

Lemma first_box_typ : forall G, G ⊢(L0) first_box ∈ □TNat.
  intros.
  cbv.
  repeat econstructor.
Qed.

Hint Unfold isvalue isplain substitute.

Lemma first_box_ev : evaluates (Quote (Splice first_box : TNat) : □TNat) (box_const 0).
  cbv in *.
  eapply star_step.
  - do 2 econstructor.
    do 2 econstructor; eauto.
  - eapply star_step.
    + econstructor.
      econstructor.
      unfold substitute. simpl_subst_all.
      econstructor; eauto.
    + eapply star_step.
      econstructor.
      unfold substitute.
      assert (closed 0 (Quote (Nat 0 : TNat))).
      * unfold closed. eauto.
      * shift_closed. eauto.
        simpl_subst_all. econstructor; eauto.
      * constructor.
Qed.

Lemma first_box_inctx_typ : forall G, G ⊢(L0) (run_in_ctx first_box) ∈ □TNat.
  intro. cbv.
  repeat econstructor.
Qed.

Lemma first_box_inctx :
  evaluates
    (run_in_ctx first_box)
    (in_ctx (const 0)).
  cbv in *.

  eapply star_step.
  do 6 econstructor.
  do 2 constructor; eauto.

  eapply star_step.
  do 6 econstructor.
  unfold substitute. simpl_subst_all.
  assert (shift 0 (Quote (Nat 0 : TNat)) = (Quote (Nat 0 : TNat))).
  eauto.
  rewrite H.
  constructor; eauto.

  unfold substitute. simpl_subst_all.

  eapply star_step.
  do 6 econstructor.
  eauto.

  constructor.
Qed.

Ltac push_subst := simpl_subst_all; simpl_lift_all.
(* and now we try executing the simpler, failing case - snd *)

Definition rev_snd_id := (run_in_ctx (App rev (Quote code_snd : □TNat) : □TNat)).

Lemma rev_snd_id_typ : ∅ ⊢(L0) rev_snd_id ∈ □TNat.
  cbv.
  repeat econstructor.
Qed.

Lemma rev_snd_id_ev :
  evaluates
    rev_snd_id
    (in_ctx code_snd).
  cbv in *.

  eapply star_step.
  repeat econstructor.

  eapply star_step.
  unfold substitute. simpl_subst_all.
  repeat push_subst.

  repeat econstructor.

  eapply star_step.
  unfold substitute.
  simpl_lift_all.
  repeat econstructor.
  repeat push_subst.

  econstructor; eauto.
  cbn. eauto.
  cbn.

  eapply star_step.
  repeat econstructor.
  unfold substitute.
  simpl_subst_all. cbn. simpl_lift_all.
  simpl_subst_all. fold traverse_term.
  simpl_subst_all.

  eapply E_PatVar_Fail; eauto.
  congruence.

  eapply star_step.
  repeat econstructor.

  eapply star_refl.
Qed.

Definition rev_fst_id := (run_in_ctx (App rev (Quote code_fst : □TNat) : □TNat)).

Lemma rev_fst_id_typ : ∅ ⊢(L0) rev_fst_id ∈ □TNat.
  cbv.
  repeat econstructor.
Qed.

Definition code_fst_rev := App (App (VAR 1 : funtype) (const 2) : TNat ==> TNat) (const 1) : TNat.
Lemma rev_fst_id_ev :
  evaluates
    rev_fst_id
    (in_ctx code_fst_rev).
  cbv in *.

  eapply star_step.
  repeat econstructor.

  eapply star_step.
  unfold substitute. simpl_subst_all.
  repeat push_subst.

  repeat econstructor.

  eapply star_step.
  unfold substitute.
  simpl_lift_all.
  repeat econstructor.
  repeat push_subst.

  econstructor; eauto.
  cbn. eauto.
  cbn.

  eapply star_step.
  repeat econstructor.
  simpl_subst_all. cbn. simpl_lift_all.
  unfold substitute.
  simpl_subst_all. fold traverse_term.
  simpl_subst_all.

  econstructor; eauto.

  eapply star_step.
  do 5 econstructor.
  eapply E_Unbox.
  repeat econstructor.

  eapply star_step.
  do 5 econstructor.
  eapply E_Unbox.
  econstructor.
  eapply E_App2.
  econstructor; eauto.

  eapply star_step.
  do 5 econstructor. eapply E_Unbox. do 2 econstructor.
  eapply E_App2.
  econstructor; eauto.

  eapply star_step.
  repeat econstructor.

  eapply star_refl.
Qed.

Lemma mini_preservation :
  exists t,
    rev_fst_id -->(L0) t /\ ∅ ⊢(L0) t ∈ □TNat.
  cbv.
  eexists.
  constructor.
  - repeat econstructor.
  -
    unfold substitute.
    repeat push_subst.
    repeat econstructor.
Qed.

(* Finally test the lambda unpacking *)

Definition LamTest := MatchLam (Quote (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) : □(TNat ==> TNat)) (TNat ==> TNat) (App (VAR 0 : □TNat ==> □TNat) (box_const 42) : □TNat) (box_const 1) : □TNat.

Lemma LamTestTyp : forall G, G ⊢(L0) LamTest ∈ □TNat.
  intros.
  repeat econstructor.
Qed.

Lemma LamTestEval : evaluates LamTest (box_const 42).
  cbv.
  eapply star_step.
  repeat econstructor.
  cbn.

  eapply star_step.
  repeat push_subst.

  econstructor; eauto.

  eapply star_step.
  unfold substitute. push_subst.
  repeat econstructor.

  eauto.
Qed.

Definition Loop := Fix (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) : TNat.

Lemma LoopTypes : forall G, G ⊢(L0) Loop ∈ TNat.
  intro.
  repeat econstructor.
Qed.

Lemma LoopDiverges : Loop -->(L0) Loop.
  cbv.
  econstructor.
  unfold substitute.
  simpl_subst_all.
  auto.
Qed.

Definition FixMatch := (MatchFix (Quote Loop : □TNat) (const 1) (const 0) : TNat).

Lemma FixMatchTypes : ∅ ⊢(L0) FixMatch ∈ TNat.
  cbv.
  repeat econstructor.
Qed.

Lemma FixMatchSucceeds : FixMatch -->(L0) const 1.
  cbv.
  repeat econstructor.
Qed.
