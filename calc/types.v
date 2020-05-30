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
| T_Fix : forall L G t T,
    G ⊢(L) t ∈ T ==> T ->
    G ⊢(L) (Fix t : T) ∈ T
| T_Lift : forall G t,
    G ⊢(L0) t ∈ TNat ->
    G ⊢(L0) (Lift t : □TNat) ∈ □TNat
| T_Box : forall G t T,
    G ⊢(L1) t ∈ T ->
    G ⊢(L0) (Quote t : □T) ∈ □T
| T_Unbox : forall G t T,
    G ⊢(L0) t ∈ □T ->
    G ⊢(L1) (Splice t : T) ∈ T
| T_Pat_Nat : forall G e n es ef T,
    G ⊢(L0) e ∈ □TNat ->
    G ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchNat e n es ef : T) ∈ T
| T_Pat_Var : forall G e x es ef T T1,
    G ⊢(L0) e ∈ □T1 ->
    lookup x G = Some (L1, T1) ->
    G ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchVar e (VAR x) es ef : T) ∈ T
| T_Pat_App : forall G e es ef T T1 T2 T3,
    T1 = T2 ==> T3 ->
    G ⊢(L0) e ∈ □T3 ->
    (insert 0 (L0, □T2) (insert 0 (L0, □(T1)) G)) ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchApp e T1 T2 es ef : T) ∈ T
| T_Pat_Unlift : forall G e es ef T,
    G ⊢(L0) e ∈ □TNat ->
    (insert 0 (L0, TNat) G) ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchUnlift e es ef : T) ∈ T
| T_Pat_Lam : forall G e es ef T T1 T2,
    G ⊢(L0) e ∈ □(T1 ==> T2) ->
    (insert 0 (L0, (□T1) ==> (□T2)) G) ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchLam e (T1 ==> T2) es ef : T) ∈ T
| T_Pat_Fix : forall G e es ef T T1,
    G ⊢(L0) e ∈ □(T1) ->
    (insert 0 (L0, □(T1 ==> T1)) G) ⊢(L0) es ∈ T ->
    G ⊢(L0) ef ∈ T ->
    G ⊢(L0) (MatchFix e es ef : T) ∈ T
where "G '⊢(' L ')' t '∈' T" := (typing_judgement G L t T).
Hint Constructors typing_judgement.

