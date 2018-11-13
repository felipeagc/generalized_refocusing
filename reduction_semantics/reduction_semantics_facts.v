Require Import Util
               reduction_languages_facts.




Module Type DET_RED_MINI_SEM.

  Include RED_MINI_LANG.


  Parameter contract : forall {k}, redex k -> option term.


  Inductive decomp k : Type :=
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

  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].

  Notation "k |~ t1 → t2"  := (reduce k t1 t2) 
                                         (no associativity, at level 70, t1 at level 69).


  Axiom dec_is_det : forall {t k} {d d0 : decomp k}, 
                         dec t k d -> dec t k d0 -> d = d0.

End DET_RED_MINI_SEM.




Module DET_RED_SEM_Facts (R : DET_RED_MINI_SEM).

  Module RF := RED_LANG_Facts R.
  Import R RF.


  Lemma reduce_is_det :                                                forall t1 t2 t3 k,
      k |~ t1 → t2  ->  k |~ t1 → t3  ->  t2 = t3.

  Proof.
    intros t1 t2 t3 k H H0.
    destruct H  as [k2 [c1 [r1 [t1' [G  [G0 G1]]]]]],
             H0 as [k3 [c2 [r2 [t2' [G2 [G3 G4]]]]]];
    subst.
    assert (H : d_red r1 c1 = d_red r2 c2) by eauto using dec_is_det.
    inversion H; dep_subst.
    congruence.
 Qed.


  Lemma reduce_red :                 forall {k1 k2} (c : context k1 k2) (r : redex k2) t,
      k1 |~ c[r] → t  ->  exists t', contract r = Some t' /\ t = c[t'].

  Proof.
    intros k1 k2 c r t H.
    destruct H as [k' [c' [r' [t' [H0 [H1 H2]]]]]].

    assert (H3 : d_red r c = d_red r' c').
    { eapply dec_is_det; solve [reflexivity | unfold dec; eauto]. }
    inversion H3; dep_subst.
    eauto.
  Qed.

End DET_RED_SEM_Facts.

