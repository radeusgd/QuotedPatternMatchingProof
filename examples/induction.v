Inductive Typed :=
| typed (u: Untyped) (T: Type)
with
Untyped :=
| leaf
| branch (t1 t2 : Typed).

Print Typed_ind.

Scheme Typed_mutualind := Induction for Typed Sort Prop
  with Untyped_mutualind := Induction for Untyped Sort Prop.
Print Typed_mutualind.

Lemma Typed_syntactic :
  forall (P : Typed -> Prop),
    (forall T, P (typed leaf T)) ->
    (forall (t1 t2 : Typed) T, P t1 ->  P t2 -> P (typed (branch t1 t2) T)) ->
    forall t : Typed, P t.
  intros.
  eapply Typed_mutualind.
  intro. intro Hp. exact Hp.
  auto.
  intros. intro. auto.
Qed.
