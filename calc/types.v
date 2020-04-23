Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.

Require Import syntax.

(* TYPES *)

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

Reserved Notation "G '⊢p' p '∈' T '~~>' Gp" (at level 40, T at level 59).
Inductive pattern_typing : TypEnv -> pattrn -> type -> list (Level * type) -> Prop :=
| T_Pat_Nat : forall G n,
    G ⊢p (PNatLit n) ∈ TNat ~~> nil
| T_Pat_Var : forall G x T,
    lookup x G = Some (L1, T) ->
    G ⊢p (PVar x) ∈ T ~~> nil
(* T_Pat_Fix : TODO *)
| T_Pat_App : forall G T1 T2,
    G ⊢p (PBindApp (T1 ==> T2) T1) ∈ T2 ~~>
      cons (L0, □(T1 ==> T2)) (cons (L0, □T1) nil)
| T_Pat_Unlift : forall G,
    G ⊢p (PBindUnlift) ∈ TNat ~~> cons (L0, TNat) nil
| T_Pat_Abs : forall G T1 T2,
    G ⊢p (PBindLam (T1 ==> T2)) ∈ (T1 ==> T2) ~~> cons (L0, ((□T1) ==> (□T2))) nil
where "G '⊢p' p '∈' T '~~>' Gp" := (pattern_typing G p T Gp).
Hint Constructors pattern_typing.

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
    G ⊢(L0) (Lift t : □TNat) ∈ □TNat
| T_Box : forall G t T,
    G ⊢(L1) t ∈ T ->
    G ⊢(L0) (Quote t : □T) ∈ □T
| T_Unbox : forall G t T,
    G ⊢(L0) t ∈ □T ->
    G ⊢(L1) (Splice t : T) ∈ T
(* | T_Fix : TODO *)
| T_Pat : forall G t1 ts tf T1 T p Gp,
    G ⊢(L0) t1 ∈ □T1 ->
    G ⊢p p ∈ T1 ~~> Gp ->
    (concat G Gp) ⊢(L0) ts ∈ T ->
    G ⊢(L0) tf ∈ T ->
    G ⊢(L0) (PatternMatch t1 p ts tf : T) ∈ T
where "G '⊢(' L ')' t '∈' T" := (typing_judgement G L t T).
Hint Constructors typing_judgement.

Definition id_nat := (Lam TNat (VAR 0 : TNat) : TNat ==> TNat).
Lemma TypingIdTest : ∅ ⊢(L0) (Lam TNat (VAR 0 : TNat) : TNat ==> TNat) ∈ TNat ==> TNat.
  auto.
Qed.
