Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Coq.Bool.Bool.

Require Import syntax.
Require Import types.
(* SEMANTICS *)

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

Definition isplain t := (decide_isplain t) = true.

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

Definition isvalue t := (decide_isvalue t) = true.

Definition LiftLambda (argT : type) (body : typedterm) (retT : type) :=
  let body' := shift 1 body in (* we need to shift to preserve original variable mapping after we do the subst that replaces x1 with $x3 *)
  let z := Quote (body'.[Splice (VAR 0 : □argT) : argT/]) in
  (Lam (□argT) (z : □retT) : ((□argT) ==> (□retT)))
.

Lemma LiftLambdaTest : (LiftLambda TNat (App (VAR 1 : TNat ==> TNat) (VAR 0 : TNat) : TNat) TNat) = (Lam (□TNat) (Quote (App (VAR 1 : TNat ==> TNat) (Splice (VAR 0 : □TNat) : TNat) : TNat) : □TNat) : □TNat ==> □TNat).
  auto.
Qed.


(* I don't check if the term is plain, I just assume it in the reduction rule before using Match *)
Definition Match (t : typedterm) (p : pattrn) : option (typedterm -> typedterm) :=
  match (t, p) with
  | (Nat n : TNat, PNatLit n') =>
    if Nat.eq_dec n n' then
      Some (fun t => t)
    else None
  | (VAR x : T,  PVar x') =>
    if Nat.eq_dec x x' then
      Some (fun t => t)
    else None
(* TODO  fixpoint *)
  | (App (e1 : T1) (e2 : T2) : T,  PBindApp T1' T2') =>
    if (type_beq T1 T1') && (type_beq T2 T2') then
      Some (fun t => t.[e1 : T1/].[e2 : T2/])
    else None
  | (Nat n : TNat, PBindUnlift) =>
    Some (fun t => t.[Nat n : TNat/])
  | (Lam argT body : T1 ==> T2, PBindLam T) =>
    if type_beq (T1 ==> T2) T && type_beq argT T1 then
      let lifted := LiftLambda argT body T2 in
      Some (fun t => t.[lifted/])
    else None
  | _ => None
  end.

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
| E_Splice : forall t T,
    isplain t -> (Splice (Quote t : □T) : T) -->(L1) t
| E_Lift_Red : forall n TN T,
    (Lift (Nat n : TN) : T) -->(L0) (Quote (Nat n : TN) : T)
| E_Lift : forall t t' T,
    t -->(L0) t' ->
    (Lift t : T) -->(L0) (Lift t' : T)
| E_Beta : forall t T1 T2 v t',
    isvalue v ->
    t' = t.[v/] ->
    (App (Lam T1 t : (T1 ==> T2)) v : T2) -->(L0) t'
(* | E_Fix : TODO *)
(* | E_Fix_Red : TODO *)
| E_Pat : forall T t1 p s f t1',
    t1 -->(L0) t1' ->
    (PatternMatch t1 p s f : T) -->(L0) (PatternMatch t1' p s f : T)
| E_Pat_Succ : forall t Ts T p s f σ s',
    isplain t ->
    Match t p = Some σ ->
    s' = σ(s) ->
    (PatternMatch (Quote t : □Ts) p s f : T) -->(L0) s'
| E_Pat_Fail : forall t Ts T p s f,
    isplain t ->
    Match t p = None ->
    (PatternMatch (Quote t : □Ts) p s f : T) -->(L0) f
where "t1 '-->(' L ')' t2" := (reducts L t1 t2).
Hint Constructors reducts.

Inductive evaluates : typedterm -> typedterm -> Prop :=
| star_refl : forall t, evaluates t t
| star_step : forall t1 t2 t3, t1 -->(L0) t2 -> evaluates t2 t3 -> evaluates t1 t3.
Hint Constructors evaluates.

Lemma test_red : evaluates (App id_nat (Nat 42 : TNat) : TNat) (Nat 42 : TNat).
  econstructor; eauto.
  econstructor; eauto.
  cbv. auto.
Qed.
