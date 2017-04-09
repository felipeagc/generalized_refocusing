Require Import Util.
Require Import Program.
Require Import Eqdep.




Module Type RED_MINI_LANG.

 Parameters 
  (term         : Set)
  (ckind        : Set)
  (elem_context_kinded : ckind -> ckind -> Set)
  (elem_plug     : forall {k1 k2}, term -> elem_context_kinded k1 k2 -> term)
  (redex         : ckind -> Set)
  (value         : ckind -> Set)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term).

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons :                                                                forall {k2 k3}
            (ec : elem_context_kinded k2 k3), context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1} {k2} {k3} _ _.
  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Axioms
  (value_trivial1 :                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v -> 
           exists (v' : value k2), t = v').

End RED_MINI_LANG.





Module RED_LANG_Facts (R : RED_MINI_LANG).

  Import R.


  (* Contexts *)

  Lemma ccons_inj :                                    forall {k1 k2} (c : context k1 k2)
                                                {k2' k3} (ec : elem_context_kinded k2 k3)
                                (ec' : elem_context_kinded k2' k3) (c' : context k1 k2'),

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


  Ltac inversion_ccons H :=

      match type of H with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H0 := fresh in 
      assert (H0 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));

      [ apply JMeq_eq_depT; eauto

      | inversion H0; dep_subst; clear H0 ]

      end.


  Lemma plug_empty : forall t k, [.](k)[t] = t.
  Proof. intuition. Qed.


  Lemma compose_empty : forall {k1 k2} (c : context k1 k2), c = c ~+ [.].
  Proof.
    induction c.
    - trivial.
    - simpl; rewrite <- IHc; trivial.
  Qed.


  Lemma plug_compose  : 
      forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t, 
          (c0 ~+ c1)[t] = c1[c0[t]].
  Proof.
    induction c0; intros.
    - auto.
    - apply IHc0.
  Qed.

  Lemma context_cons_snoc :                                            forall {k1 k2 k3},

      forall (c0 : context k1 k2) (ec0 : elem_context_kinded k2 k3), 
          exists {k4} (ec1 : elem_context_kinded k1 k4) (c1 : context k4 k3), 
              (ec0=:c0) = (c1~+ec1=:[.]).

  Proof.
    intros k1 k2 k3 c0; revert k3.
    induction c0; intros.
    - exists k3; exists ec0; eexists [.]; trivial.
    - edestruct IHc0 with k3 ec as (k4, (ec1, (c1, IH))).
    rewrite IH; exists k4; exists ec1; exists (ec0 =: c1); trivial.
  Qed.



  Lemma mid_ccons_as_append :                   forall {k1 k2 k3 k4} (c1 : context k1 k2)
                                   (ec : elem_context_kinded k2 k3) (c2 : context k3 k4),

      c2 ~+ ec =: c1  =  c2 ~+ (ec =: [.]) ~+ c1.

  Proof.
    intros k1 k2 k3 k4 c1 ec c2.
    induction c2;
    solve [ auto ].
  Qed.


  Lemma append_assoc :      forall {k4 k3} (c1 : context k3 k4) {k2} (c2 : context k2 k3)
                                                               {k1} (c3 : context k1 k2),
      c1 ~+ c2 ~+ c3 = (c1 ~+ c2) ~+ c3.

  Proof.
    induction c1; intros; 
    solve [simpl; f_equal; eauto].
  Qed.


  Lemma ccons_append_empty_self_JM :                                   forall {k1 k2 k3},

      forall (c1 : context k1 k2) (c2 : context k2 k3), 
          k2 = k3 -> c1 ~= c2 ~+ c1 -> c2 ~= [.](k2).

  Proof with eauto.
    intros k1 k2 k3 c1; revert k3.
    induction c1 as [ | k k' ec c1]; 
        intros k3 c2 H H0;
        destruct c2 as [ | k0 k0' ec0 c2]...
    - discriminateJM H0.
    - exfalso.
      simpl in H0.

(* MODIFIED: unfolded inversion_ccons H0 *)
match type of H0 with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H1 := fresh in 
      assert (H1 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));
      [ apply JMeq_eq_depT; eauto

      | inversion H1 ] end.
dependent_destruction2 H8.
clear H1.
rename ec0 into ec.
(* END inversion_ccons H0.*)
      assert (H1 : c2 ~+ ec =: [.](k0) ~= [.](k0)). 
      {
          eapply IHc1...
          rewrite <- append_assoc. 
          rewrite <- (mid_ccons_as_append c1 ec c2).
          replace (c2 ~+ ec =: c1) with c1 by auto.
          reflexivity.
      }
      revert H1; clear; revert c2.
      cut (forall k (c : context k0' k), 
               k = k0 -> ~ (c ~+ ec =: [.](k0) ~= [.](k0))).
      { intros H c2 H1; eapply H... }
      intros k c G H.
      destruct c; 
      discriminateJM H.
  Qed.


  Lemma ccons_append_empty_self :                     forall {k1 k2} (c1 : context k1 k2)
                                                                    (c2 : context k2 k2),
      c1 = c2 ~+ c1 -> c2 = [.](k2).

  Proof with eauto. 
    intros k1 k2 c1 c2 H.
    cut (c2 ~= [.](k2)).
    { intro H0; rewrite H0... }
    eapply ccons_append_empty_self_JM with c1...
    rewrite <- H.
    reflexivity.
  Qed.



  (* Values *)

  Lemma value_trivial :               forall {k} (v : value k) {k'} (c : context k k') t,

      c[t] = v -> exists (v' : value k'), t = v'.

  Proof.
    intros k v k' c t; revert t.
    induction c;
        intros t H0.
    - eauto.
    - destruct (IHc ec:[t]) as [v' H1];
    try solve [eauto |
    try rec_subst H1; eauto using value_trivial1 ].
  Qed.



End RED_LANG_Facts.




Module Type RED_MINI_LANG2.

  Include RED_MINI_LANG.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
     t = d.

  Axioms
  (decompose :                                                                forall t k,
       exists d : decomp k, dec t k d)

  (value_redex :                                  forall {k} (v : value k) (r : redex k),
       value_to_term v <> redex_to_term r).

End RED_MINI_LANG2.




Module RED_LANG2_Facts (R : RED_MINI_LANG2).

  Import R.


  Definition only_trivial_dec t k :=                                        forall t' k',
      forall (c : context k k'), c[t'] = t -> 
          k = k' /\ [.](k) ~= c \/ exists (v : value k'), t' = v.


  Lemma trivial_val_red :                                                     forall t k,
      only_trivial_dec t k ->
          (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).

  Proof with eauto.
    intros t k H0.
    destruct (decompose t k) as [[k' r c | v]].
    - destruct (H0 r _ c) as [[H2 H3] | [v H2]]; dep_subst.
      + symmetry; apply H.
      + right. exists r; apply H.
      + symmetry in H2. apply value_redex in H2. autof.
    - left. exists v; apply H.
  Qed.

End RED_LANG2_Facts.




Module Type RED_MINI_LANG_WD <: RED_MINI_LANG.

  Include RED_MINI_LANG.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
      t = d.

End RED_MINI_LANG_WD.



Module RedDecProcEqvDec (R : RED_MINI_LANG_WD).

  Module RF := RED_LANG_Facts R.
  Import R RF.


  Section S.

  Variable dec_proc : forall {k1 k2}, term -> context k1 k2 -> decomp k1 -> Prop.
  Arguments dec_proc {k1 k2} _ _ _.


  Hypothesis
  (dec_proc_correct :                             forall {k1 k2} t (c : context k1 k2) d,
       dec_proc t c d -> c[t] = d)

  (dec_proc_plug :        forall {k1 k2 k3} (c : context k1 k2) (c0 : context k3 k1) t d,
       dec_proc c[t] c0 d -> dec_proc t (c ~+ c0) d)

  (dec_proc_plug_rev :    forall {k1 k2 k3} (c : context k1 k2) (c0 : context k3 k1) t d,
       dec_proc t (c ~+ c0) d -> dec_proc c[t] c0 d)

  (dec_proc_redex_self :               forall {k1 k2} (r : redex k2) (c : context k1 k2),
       dec_proc r c (d_red r c))

  (dec_proc_value_self :                                        forall {k} (v : value k),
      dec_proc v [.] (d_val v)).



  Theorem dec_proc_eqv_dec :                      forall {k1 k2} t (c : context k1 k2) d,
      (dec_proc t c d <-> dec c[t] k1 d).

  Proof with eauto.
    intros ? ? ? c d.
    split; intro H.
    - apply dec_proc_correct...
    - rewrite (compose_empty c).
      apply dec_proc_plug...
      rewrite H.
      destruct d.
      + apply dec_proc_plug_rev...
        rewrite <- compose_empty.
        apply dec_proc_redex_self.
      + apply dec_proc_value_self...
  Qed.

  End S.

End RedDecProcEqvDec.

