Require Import Util.
Require Import Program.
Require Import Eqdep.

Section Path.
  Variable vertex : Type.
  Variable edge   : vertex -> vertex -> Type.

  Inductive path (k1 : vertex) : vertex -> Type :=
  | empty : path k1 k1
  | pcons : forall {k2 k3} (ec : edge k2 k3), path k1 k2 -> path k1 k3.

  Arguments empty {k1}.
  Arguments pcons {k1 k2 k3} _ _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := pcons (at level 60, right associativity).

  Lemma pcons_inj : forall {k1 k2} (c : path k1 k2) {k2' k3} (ec : edge k2 k3)
                                        (ec' : edge k2' k3) (c' : path k1 k2'),

          ec=:c ~= ec'=:c' ->
          JMeq ec ec' /\ k2 = k2' /\ c ~= c'.

  Proof.
    intros.
    assert (H1 := JMeq_eq_depT _ _ _ _ _ (refl_equal _) H).
    assert (H2 := eq_dep_eq_sigT _ _ _ _ _ _ H1). 
    inversion H2; subst.
    dep_subst.
    auto.
  Qed.

  Fixpoint compose {k1 k2} (p0 : path k1 k2) {k3} (p1 : path k3 k1) : path k3 k2 :=
    match p0 in (path _ y0) return (path k3 y0) with
    | [.]      => p1
    | e =: p0' => e =: (compose p0' p1)
    end.
  Infix "~+" := compose (at level 60, right associativity).

  Lemma compose_empty : forall {k1 k2} (c : path k1 k2), c = c ~+ [.].
  Proof.
    induction c.
    - trivial.
    - simpl; rewrite <- IHc; trivial.
  Qed.

  Lemma compose_assoc : forall {k4 k3} (c1 : path k3 k4) {k2} (c2 : path k2 k3)
                                                         {k1} (c3 : path k1 k2),
      c1 ~+ c2 ~+ c3 = (c1 ~+ c2) ~+ c3.
  Proof.
    induction c1; intros; 
    solve [simpl; f_equal; eauto].
  Qed.

  Lemma path_cons_snoc :                                     forall {k1 k2 k3},

      forall (c0 : path k1 k2) (ec0 : edge k2 k3), 
          exists {k4} (ec1 : edge k1 k4) (c1 : path k4 k3),
              (ec0=:c0) = (c1~+ec1=:[.]).

  Proof.
    intros k1 k2 k3 c0. revert k3.
    induction c0; intros.
    - exists k3; exists ec0; eexists [.]; trivial.
    - edestruct IHc0 with k3 ec as (k4, (ec1, (c1, IH))).
    rewrite IH; exists k4; exists ec1; exists (ec0 =: c1); trivial.
  Qed.

  Lemma mid_pcons_as_append : forall {k1 k2 k3 k4} (c1 : path k1 k2)
                                 (ec : edge k2 k3) (c2 : path k3 k4),

      c2 ~+ ec =: c1  =  c2 ~+ (ec =: [.]) ~+ c1.

  Proof.
    intros k1 k2 k3 k4 c1 ec c2.
    induction c2;
    solve [ auto ].
  Qed.

  (* Inversion *)

  Ltac inversion_pcons H :=

      match type of H with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H0 := fresh in 
      assert (H0 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));

      [ apply JMeq_eq_depT; eauto

      | inversion H0; dep_subst; clear H0 ]

      end.


  Lemma pcons_append_empty_self_JM :                         forall {k1 k2 k3},

      forall (c1 : path k1 k2) (c2 : path k2 k3), 
          k2 = k3 -> c1 ~= c2 ~+ c1 -> c2 ~= [.](k2).

  Proof with eauto.
    intros k1 k2 k3 c1; revert k3.
    induction c1 as [ | k k' ec c1]; 
        intros k3 c2 H H0;
        destruct c2 as [ | k0 k0' ec0 c2]...
    - discriminateJM H0.
    - exfalso.
      simpl in H0.

(* MODIFIED: unfolded inversion_pcons H0 *)
match type of H0 with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H1 := fresh in 
      assert (H1 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));
      [ apply JMeq_eq_depT; eauto

      | inversion H1 ] end.
dependent_destruction2 H8.
clear H1.
rename ec0 into ec.
(* END inversion_pcons H0.*)
      assert (H1 : c2 ~+ ec =: [.](k0) ~= [.](k0)). 
      {
          eapply IHc1...
          rewrite <- compose_assoc. 
          rewrite <- (mid_pcons_as_append c1 ec c2).
          replace (c2 ~+ ec =: c1) with c1 by auto.
          reflexivity.
      }
      revert H1; clear; revert c2.
      cut (forall k (c : path k0' k), 
               k = k0 -> ~ (c ~+ ec =: [.](k0) ~= [.](k0))).
      { intros H c2 H1; eapply H... }
      intros k c G H.
      destruct c; 
      discriminateJM H.
  Qed.

  Lemma pcons_append_empty_self :              forall {k1 k2} (c1 : path k1 k2)
                                                              (c2 : path k2 k2),
      c1 = c2 ~+ c1 -> c2 = [.].

  Proof with eauto. 
    intros k1 k2 c1 c2 H.
    cut (c2 ~= [.](k2)).
    { intro H0; rewrite H0... }
    eapply pcons_append_empty_self_JM with c1...
    rewrite <- H.
    reflexivity.
  Qed.

  (* Path action *)

  Fixpoint path_action_dep {T : vertex -> Type}
                           (edge_action : forall x y, T y -> edge x y -> T x)
                           {k1 k2} (t : T k2) (p : path k1 k2) : T k1:=
  match p in (path _ v) return (T v -> T k1) with
  | [.]   => fun t0 => t0
  | e=:p' => fun t0 => path_action_dep edge_action (edge_action _ _ t0 e) p'
  end t.

  Section Path_action.
    Variable T : Type.
    Variable edge_action : forall x y, T -> edge x y -> T.

    Fixpoint path_action {k1 k2} (t : T) (p : path k1 k2) : T :=
       match p with
      | [.]   => t
      | e=:p' => path_action (edge_action _ _ t e) p'
      end.

    Notation "c [ t ]" := (path_action t c) (at level 0).

    Lemma action_empty : forall (t : T) {k1 : vertex}, [.](k1)[t] = t.
    Proof. intuition. Qed.

    Lemma action_compose :
      forall {k1 k2 k3} (c0 : path k1 k2) (c1 : path k3 k1) t,
          (c0 ~+ c1)[t] = c1[c0[t]].
    Proof.
      induction c0; intros.
      - auto.
      - apply IHc0.
    Qed.

  End Path_action.

End Path.

Arguments path  {vertex} edge _ _.
Arguments empty {vertex edge k1}.
Arguments pcons {vertex edge k1 k2 k3} _ _.
Arguments compose {vertex edge k1 k2} _ {k3} _.
Arguments path_action {vertex edge T} edge_action {k1 k2} t p.

Notation "[.]"      := empty.
Infix    "=:"       := pcons (at level 60, right associativity).
Infix    "~+"       := compose (at level 60, right associativity).
