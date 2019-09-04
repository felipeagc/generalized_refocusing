Require Import Util.
Require Import Program.
Require Import Eqdep.
Require Import path.
Require Import reduction_semantics.




Module Type RED_MINI_LANG_WD.

  Include RED_MINI_LANG.
  Include RED_MINI_LANG_Notions.

  Axioms
  (value_trivial1 :                    forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v -> 
           exists (v' : value k2), t = v').

End RED_MINI_LANG_WD.


Module RED_LANG_Facts (Import R : RED_MINI_LANG_WD).

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




Module RedDecProcEqvDec (Import R : RED_MINI_LANG_WD).

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

