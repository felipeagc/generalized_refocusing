Require Import Util.
Require Import Program.
Require Import Eqdep.
Require Import path.




Module Type RED_MINI_LANG.

 Parameters 
  (term         : Type)
  (ckind        : Type)
  (elem_context_kinded : ckind -> ckind -> Type)
  (elem_plug     : forall {k1 k2}, term -> elem_context_kinded k1 k2 -> term)
  (redex         : ckind -> Type)
  (value         : ckind -> Type)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term).

  Notation "[.]( k )" := (@empty _ elem_context_kinded k).

  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.

  Definition context : ckind -> ckind -> Type := path elem_context_kinded.

  Definition plug t {k1 k2} (c : context k1 k2) : term :=
    path_action (@elem_plug) t c.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Axioms
  (value_trivial1 :                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v -> 
           exists (v' : value k2), t = v').

End RED_MINI_LANG.


Module RED_LANG_Facts (R : RED_MINI_LANG).

  Import R.

  Definition plug_empty : forall t k, [.](k)[t] = t :=
    @action_empty _ _ _ (@elem_plug).

  Definition plug_compose : forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t,
          (c0 ~+ c1)[t] = c1[c0[t]] :=
    @action_compose _ _ _ (@elem_plug).

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
    - rewrite (compose_empty _ _ c).
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

