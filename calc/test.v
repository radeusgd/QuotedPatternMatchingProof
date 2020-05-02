Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.
Require Import Coq.Bool.Bool.

Require Import syntax.
Require Import types.
Require Import semantics.

(* simple 'Unit test' *)
Definition UnliftConstant := (PatternMatch (Quote (Nat 42 : TNat) : □TNat) (PBindUnlift) (VAR 0 : TNat) (Nat 1 : TNat) : TNat).
Lemma UnliftConstantTypechecks : ∅ ⊢(L0) UnliftConstant ∈ TNat.
  econstructor; eauto.
Qed.
Lemma UnliftConstantEvaluates : UnliftConstant -->(L0) (Nat 42 : TNat).
  econstructor; cbv; eauto.
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

Definition const (n : nat):= (Nat n : TNat).
Definition box_const (n : nat) := (Quote (const n) : □TNat).
Hint Unfold const box_const.

Definition funtype := (TNat ==> (TNat ==> TNat)).
Definition fun_fst := (Lam TNat (Lam TNat (VAR 1 : TNat) : TNat ==> TNat) : TNat ==> (TNat ==> TNat)).
Definition fun_snd := (Lam TNat (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) : TNat ==> (TNat ==> TNat)).
Definition code_fst := App (App (VAR 1 : funtype) (const 1) : TNat ==> TNat) (const 2) : TNat.
Definition code_snd := App (App (VAR 0 : funtype) (const 1) : TNat ==> TNat) (const 2) : TNat.
Definition rev :=
  (Lam (□TNat) (
         (PatternMatch (VAR 0 : □TNat)
                       (PBindApp (TNat ==> TNat) TNat)
                       (PatternMatch (VAR 1 : □(TNat ==> TNat))
                                     (PBindApp funtype TNat)
                                     (PatternMatch (VAR 1 : □(TNat ==> (TNat ==> TNat)))
                                                   (PVar 6)
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
Hint Unfold pattern_binders_count.

Ltac push_subst := simpl_subst_all; simpl_lift_all; try unfold pattern_binders_count.
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
  cbv. eauto.
  cbv.

  eapply star_step.
  repeat econstructor.
  



  (* reached failure but not for the right reason *)
Admitted.
