Require Import List.
Require Import ListSet.

Section Subset.

Variable A : Type.
Variable eq_A : forall x y : A, {x = y} + {x <> y}.

(*** definition of subsets and some properties ***)
Definition Subset (xs ys : set A) := forall x, In x xs -> In x ys.

Hint Unfold Subset.
Hint Resolve in_or_app.

  Lemma subset_empty :
    forall (l : set A), Subset (empty_set _) l.
  Proof.
  cbv; contradiction.
  Qed.
  
  Hint Resolve subset_empty.
  
  Lemma subset_not_in :
    forall (xs ys: set A) x, Subset xs ys -> ~In x ys -> ~In x xs.
  Proof.
  intros; intro.
  elim H0.
  apply H; auto.
  Qed.
  
  Hint Resolve subset_not_in.
  
  Lemma subset_app :
    forall (xs ys l: set A), Subset xs ys -> Subset xs (l++ys).
  Proof.
  auto.
  Qed.
  
  Hint Resolve subset_app.
  
  Lemma subset_app_2 :
    forall (xs ys l: set A), Subset (xs++l) ys -> Subset xs ys.
  Proof.
  auto.
  Qed.
  
  Hint Resolve subset_app_2.
  
  Lemma subset_app_2_r :
    forall (xs ys l: set A), Subset (l++xs) ys -> Subset xs ys.
  Proof.
  auto.
  Qed.
  
  Hint Resolve subset_app_2_r.
  
  Lemma in_subset :
    forall x (xs : set A), In x xs -> Subset (set_add eq_A x (empty_set _)) xs.
  Proof.
  unfold Subset; intros.
  destruct H0; subst; auto.
  inversion H0.
  Qed.
  
  Hint Resolve in_subset.
  
  
  Lemma subset_app_in :
    forall (xs ys zs: set A), Subset xs zs -> Subset ys zs -> Subset (xs++ys) zs.
  Proof.
  unfold Subset; intros.
  elim (in_app_or _ _ _ H1); intros; eauto.
  Qed.
  
  Hint Resolve subset_app_in.
  
  Lemma subset_remove_add :
    forall (x : A) (xs ys : set A), Subset (set_remove eq_A x xs) ys -> Subset xs (set_add eq_A x ys).
  Proof.
    unfold Subset in *; intros; eauto.
    case_eq (eq_A x x0); intros; subst...
    apply set_add_intro2.
    auto.
    apply set_add_intro1.
    apply H.
    apply set_remove_3; auto.
  Qed.
  
  Lemma set_add_inversion :
    forall x (xs ys:set A), ~In x xs -> ~In x ys -> x::xs = x::ys -> xs = ys.
  Proof.
  induction xs; destruct ys; simpl; intros; auto; try discriminate.
  inversion H1; f_equal.
  Qed.

Hint Resolve set_add_inversion.
Hint Resolve set_add_intro1 set_add_intro2.

  Lemma In_split_aux :
    forall (x : A) (l : set A), NoDup l ->
    { ys : set A * set A | l = app (fst ys) (cons  x (snd ys)) /\ ~ In x (fst ys ++ snd ys)} + ( ~ In x l).
  Proof.
  induction l; simpl; intros; auto.
  assert (~In a l).
  inversion H; auto.
  assert (NoDup l) by (inversion H; auto).
  destruct (IHl H1) as [[[x1 x2] [p1 p2]] | Hneq]; simpl; subst; auto. 
  simpl in *. left.
  exists (pair (a::x1) x2).
  split; eauto.
  simpl.
  intro.
  destruct H2; subst; eauto.
  inversion H; subst. elim H4; auto.
  
  apply in_or_app.
  right; constructor; auto.
  case_eq (eq_A a x); intros; subst; eauto.
  left.
  exists (nil,l).
  simpl; split; auto.
  right.
  intro.
  destruct H3.
  auto.
  elim Hneq; auto.
  Defined.
  

  Lemma In_split :
forall (x : A) (l : set A), NoDup l ->
sumor  { ys : set A & { ll : set A & l = app ys (cons  x ll) /\ ~ In x ( ys ++ ll)}} ( ~ In x l).
Proof.
intros.
assert (hh:=In_split_aux x l H).
destruct hh.
destruct s.
destruct a.
destruct x0.
left.
exists s.
exists s0.
subst; eauto.
right.
auto.
Defined.

Inductive in_split : A -> set A -> set A -> Prop :=
| in_front : forall x xs, ~In x xs -> in_split x xs (x::xs)
| in_inside : forall x a  xs zs, in_split x xs zs ->
~In a (x::xs) ->
in_split x (a::xs) (a::zs).


Lemma in_split_inv :
forall ys x xs xs0, in_split x xs ys -> in_split x xs0 ys -> xs = xs0.
induction ys; simpl; intros; eauto.
inversion H; subst.
inversion H0; subst.
inversion H; subst.
auto.
elim H7; eauto.
left; auto.
inversion H; subst.
elim H6; eauto.
left; auto.
f_equal.
eapply IHys; eauto.
Qed.

Lemma in_split_in :
forall x xs ys, in_split x xs ys -> In x ys.
induction 1; eauto.
left; auto.
right; auto.
Qed.

Lemma in_split_inv2 :
forall ys xs x, in_split x xs ys -> exists zs, exists xs0, ys = zs ++ x::xs0 /\ zs++xs0=xs.
Proof.
induction 1; intros; eauto.
exists nil; auto.
exists xs; split; auto.
destruct IHin_split.
destruct H1.
destruct H1.
rewrite H1.
rewrite <- H2.
simpl.
exists (a::x0).
exists x1.
simpl.
split; eauto.
Qed.

Lemma in_split_split :
forall x0 x1 x, ~ In x (x0++x1) -> NoDup (x0 ++ x1) -> in_split x (x0++x1) (x0++x::x1).
Proof.
  induction x0; simpl; intros; eauto.
  constructor.
  auto.
  constructor.
  apply IHx0.
  intro.
  elim H; eauto.
  inversion H0; auto.
  intro.
  destruct H1.
  elim H; eauto.
  assert (hh:= in_app_or _ _ _ H1).
  destruct hh; eauto.
  inversion H0; eauto.
  inversion H0; auto.
Qed.

End Subset.

Arguments in_split [A].
Arguments Subset [A].
Arguments in_split_split [A].
Arguments in_split_in [A].
Arguments in_split_inv [A].
Arguments in_split_inv2 [A].
Arguments subset_not_in {A}.
Arguments subset_remove_add {A}.

Hint Resolve subset_empty.
Hint Resolve in_or_app.
Hint Resolve subset_not_in.
Hint Resolve subset_app.
Hint Resolve subset_app_2.
Hint Resolve subset_app_2_r.
Hint Resolve in_subset.
Hint Resolve subset_app_in.
Hint Resolve subset_remove_add.
Hint Resolve set_add_inversion.
Hint Resolve set_add_intro1 set_add_intro2.
Hint Resolve in_split_in.
Hint Resolve in_split_inv.
Hint Resolve in_split_inv2.
Hint Resolve set_union_nodup.
Hint Resolve set_remove_nodup.
Hint Resolve set_remove_1.
Hint Resolve set_remove_2.
Hint Resolve set_union_elim.

