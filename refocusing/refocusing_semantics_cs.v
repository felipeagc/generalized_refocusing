(*** Interface part ***)


Require Import Program
               Util
               rewriting_system
               reduction_languages_facts.
Require Export Subset
               reduction_semantics_cs
               reduction_strategy.





Module Type PRE_REF_SEM <: RED_STRATEGY_LANG.

  Include RED_STRATEGY_LANG.

  Parameter contract : forall {k}, redex k -> forall {k'}, context k' k -> option term.

  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].
  Definition subterm_order          := clos_trans_1n term immediate_subterm.
  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r c = Some t /\ t2 = c[t].

  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.

  Notation "t1 <| t2"      := (subterm_order t1 t2)      (no associativity, at level 70).

  Axioms
  (redex_trivial1 :                                        forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v)
  (wf_immediate_subterm : well_founded immediate_subterm)
  (wf_subterm_order     : well_founded subterm_order).


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End PRE_REF_SEM.

Module Type REF_STRATEGY (PR : PRE_REF_SEM) <: RED_STRATEGY PR.

  Import PR.

  Include RED_STRATEGY PR.

  Axioms 
  (wf_search :                                                                forall k t,
       well_founded (search_order k t))

  (search_order_trans :                                           forall k t ec0 ec1 ec2,
       k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2)

  (search_order_comp_if :                
                             forall t k k' k'' (ec0 : elem_context_kinded k k') 
       (ec1 : elem_context_kinded k k''),
       immediate_ec ec0 t -> immediate_ec ec1 t -> 
         k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1))

  (search_order_comp_fi :  
    forall t k k' k'' (ec0 : elem_context_kinded k k')
    (ec1 : elem_context_kinded k k''),
       k, t |~ ec0 << ec1 -> 
           immediate_ec ec0 t /\ immediate_ec ec1 t).


End REF_STRATEGY.





Module Type RED_REF_SEM <: RED_SEM.

  Declare Module R  : RED_SEM.
  Declare Module ST : RED_STRATEGY_STEP R.

  Include R.
  Export ST.


  Inductive refocus_in {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | ri_red  : forall t {k2} (c : context k1 k2) r,
                dec_term t k2 = in_red r -> 
                refocus_in t c (d_red r c)
  | ri_val  : forall t {k2} (c : context k1 k2) d v,
                dec_term t k2 = in_val v ->
                refocus_out v c d ->
                refocus_in t c d
  | ri_step : forall t {k2} (c : context k1 k2) d t0 {k3} (ec : elem_context_kinded k2 k3),
               dec_term t k2 = in_term t0 ec ->
               refocus_in t0 (ec=:c) d ->
               refocus_in t c d

  with refocus_out {k1} : forall {k2}, value k2 -> context k1 k2 -> decomp k1 -> Prop :=

  | ro_end  : forall (v : value k1),
                refocus_out v [.] (d_val v)
  | ro_red  : forall {k2 k2'} (ec : elem_context_kinded k2 k2') (c : context k1 k2) (v : value k2') r,
                dec_context ec v = in_red r ->
                refocus_out v (ec=:c) (d_red r c)
  | ro_val  : forall {k2 k2'} (ec : elem_context_kinded k2 k2') (c  : context k1 k2) (v : value k2') d v0,
                dec_context ec v = in_val v0 ->
                refocus_out v0 c d ->
                refocus_out v (ec=:c) d
  | ro_step : forall {k2 k2'}  (ec : elem_context_kinded k2 k2') (c : context k1 k2) (v : value k2') d t 
                {k2''} (ec0 : elem_context_kinded k2 k2''),
                dec_context ec v = in_term t ec0 ->
                refocus_in t (ec0=:c) d ->
                refocus_out v (ec=:c) d.

  Scheme refocus_in_Ind  := Induction for refocus_in  Sort Prop
    with refocus_out_Ind := Induction for refocus_out Sort Prop.


  Axioms
  (refocus_in_val_eqv_refocus_out :                            forall {k2} (v : value k2)
                                                              {k1} (c : context k1 k2) d,
       refocus_in v c d <-> refocus_out v c d)

  (refocus_in_eqv_dec :                           forall t {k1 k2} (c : context k1 k2) d,
      (refocus_in t c d <-> dec c[t] k1 d)). 

End RED_REF_SEM.


Module Type RED_PE_REF_SEM <: RED_REF_SEM.

  Include RED_REF_SEM.
  Import R.

  Axioms
  (dec_context_not_val :                                 forall {k k'} (ec : elem_context_kinded k k') (v1 : value k) v0,
       dec_context ec v0 <> in_val v1)
  (dec_term_value :                                             forall {k} (v : value k),
       dec_term v k = in_val v).

End RED_PE_REF_SEM.





Module REF_LANG_Help.

  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).

  Context `{term : Set}.
  Context `{immediate_subterm : term -> term -> Prop}.
  Context `{wf_immediate_subterm : well_founded immediate_subterm}.

  Ltac prove_sto_wf :=
      exact (wf_clos_trans_l _ _ wf_immediate_subterm).

  Ltac prove_ec_wf := 
      intros k t ec; destruct k, t, ec; repeat 
      (
          constructor; 
          intros ec H; 
          destruct ec; inversion H; dep_subst; clear H
      ).

End REF_LANG_Help.





(*** Implementation part ***)


Module RedRefSem (PR : PRE_REF_SEM) (ST : REF_STRATEGY PR) <: RED_REF_SEM.

  Module RLF := RED_LANG_Facts PR.
  Import PR RLF.



  Module ST := ST.
  Export ST.

  Module R <: RED_SEM.

    Include PR.

    Lemma decompose_total :        
                                        forall (t : term) k,
        exists (d : decomp k), dec t k d.

    Proof with unfold dec; eauto.
      induction t using (well_founded_ind wf_subterm_order); intros.

      remember (dec_term t k); assert (hh := dec_term_correct t k);
      symmetry in Heqi;
      destruct i; rewrite Heqi in hh.

      - exists (d_red r [.])...
      - destruct (H t0) with (k:=k');
        unfold dec in *.
        repeat econstructor...
        destruct x.
        + exists (d_red r (c~+(e=:[.]))).
          subst t0; simpl; rewrite plug_compose...

        + { subst t0.
          clear Heqi; generalize dependent v.
remember (erase_kinds e).
generalize dependent k'.
          induction e0 using (well_founded_ind (wf_search k t)); intros.

(*          induction e using (well_founded_ind (wf_search k t)); intros.
*)
          remember (dec_context e v); assert (ht := dec_context_correct e v).
          destruct i; rewrite <- Heqi in ht; try 
          ( compute in hh; rewrite <- hh in ht).

          - exists (d_red r [.])...

          - destruct (H t0) with (k := k'0).
(* as [[k2 r c | v0] [? Hd]].*)
              repeat econstructor...
              subst t0...
              destruct x...
               
            + exists (d_red r (c~+e1=:[.])).
              simpl; rewrite plug_compose...

            + symmetry in Heqi.
              destruct (dec_context_term_next _ _ _ _ Heqi) as (H5, _).
symmetry in Heqe0.
subst...

          - eexists (d_val v0)...
}

        - eexists (d_val v)...

    Qed.


  End R.

  Include R.


  Inductive refocus_in {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | ri_red  : forall t {k2} (c : context k1 k2) r,
                dec_term t k2 = in_red r -> 
                refocus_in t c (d_red r c)
  | ri_val  : forall t {k2} (c : context k1 k2) d v,
                dec_term t k2 = in_val v ->
                refocus_out v c d ->
                refocus_in t c d
  | ri_step : forall t {k2} (c : context k1 k2) d t0 {k3} (ec : elem_context_kinded k2 k3),
               dec_term t k2 = in_term t0 ec ->
               refocus_in t0 (ec=:c) d ->
               refocus_in t c d

  with refocus_out {k1} : forall {k2}, value k2 -> context k1 k2 -> decomp k1 -> Prop :=

  | ro_end  : forall (v : value k1),
                refocus_out v [.] (d_val v)
  | ro_red  : forall {k2 k2'} (ec : elem_context_kinded k2 k2') (c : context k1 k2) (v : value k2') r,
                dec_context ec v = in_red r ->
                refocus_out v (ec=:c) (d_red r c)
  | ro_val  : forall {k2 k2'} (ec : elem_context_kinded k2 k2') (c  : context k1 k2) (v : value k2') d v0,
                dec_context ec v = in_val v0 ->
                refocus_out v0 c d ->
                refocus_out v (ec=:c) d
  | ro_step : forall {k2 k2'}  (ec : elem_context_kinded k2 k2') (c : context k1 k2) (v : value k2') d t 
                {k2''} (ec0 : elem_context_kinded k2 k2''),
                dec_context ec v = in_term t ec0 ->
                refocus_in t (ec0=:c) d ->
                refocus_out v (ec=:c) d.

  Scheme refocus_in_Ind  := Induction for refocus_in  Sort Prop
    with refocus_out_Ind := Induction for refocus_out Sort Prop.





  Lemma refocus_in_correct :                      forall t {k1 k2} (c : context k1 k2) d,
      refocus_in t c d -> c[t] = d.

  Proof.
    intros t k1 k2 c d.
    induction 1 using refocus_in_Ind with
    (P := fun _ t c d (_ : refocus_in  t c d)     => c[t] = d)
    (P0:= fun _ v c d (_ : refocus_out v c d)  => c[v] = d);
    simpl; auto;
    match goal with
    | _ : dec_term ?t ?k2 = _      |- _ => assert (hh := dec_term_correct t k2)
    | _ : dec_context ?ec ?v = _ |- _ => assert (hh := dec_context_correct ec v)
    end;
    rewrite e in hh; simpl in *; 
    rewrite hh;
    solve [auto].
  Qed.


  Lemma refocus_in_to_out :        forall {k2} (v : value k2) {k1} (c : context k1 k2) d,
      refocus_in v c d -> refocus_out v c d.

  Proof with eauto.
    intros k2 v k1; remember (value_to_term v) as t; revert k2 v Heqt.
    induction t using (well_founded_ind wf_subterm_order); intros; subst.

    dependent destruction H0;
        assert (hh := dec_term_correct (v:term) k2); rewrite H in hh.

    - contradiction (value_redex _ _ hh).

    - rewrite (value_to_term_injective _ _ hh)...

    - destruct (value_trivial v (ec=:[.]) t0); auto;
          try solve [eapply dec_term_next_alive; eassumption];
          subst t0;
          capture_all value @value_to_term.

      clear H; revert x H0 hh.
remember (erase_kinds ec).
generalize dependent k3.
      induction e using (well_founded_ind (wf_search k2 (v:term))); intros.

      assert (refocus_out x (ec=:c) d).
      { apply (H1 x)... do 2 econstructor... }

      dependent destruction H2;
(*try
          assert (G1 := ccons_inj _ _ _ _ x1 x);
          subst; rec_subst G1;
*)
          assert (gg := dec_context_correct ec v0); rewrite H2 in gg.

      + contradiction (value_redex v r); congruence.

      + assert (v1 = v).
        { apply (value_to_term_injective v1 v); congruence. }
        subst...

      + destruct (value_trivial v (ec1=:[.]) t); auto;
            try solve [ simpl; congruence ];
            subst t.
        eapply (H ec1); eauto.
subst e.
        * rewrite hh; eapply dec_context_term_next; eauto.
        * congruence. 
  Qed.


  Lemma refocus_out_to_in :      forall {k2} {v : value k2} {k1} {c : context k1 k2} {d},
      refocus_out v c d -> refocus_in v c d.

  Proof with eauto.
    intros k2 v k1; remember (value_to_term v); revert k2 v Heqt.
    induction t using (well_founded_ind wf_subterm_order); intros; subst.

    remember (dec_term v k2) as i;
    assert (hh := dec_term_correct v k2);
    destruct i; rewrite <- Heqi in hh; symmetry in Heqi.

    - contradict (value_redex _ _ hh).

    - apply (ri_step _ _ _ _ _ Heqi).

      destruct (value_trivial v (e=:[.]) t);
          try solve [auto];
          subst t;
          capture_all value @value_to_term.

      clear Heqi; revert x hh.
remember (erase_kinds e).
generalize dependent k'.
      induction e0 using (well_founded_ind (wf_search k2 v)); intros.

      apply (H x) with (v := x)...
      { do 2 econstructor... }
      remember (dec_context e x) as i.
      assert (gg := dec_context_correct e x);
      destruct i; rewrite <- Heqi in gg. 
      symmetry in Heqi.

      + contradiction (value_redex v r); congruence.

      + destruct (value_trivial v (e1=:[.]) t);
            try solve [simpl; congruence];
            subst t.

        apply ro_step with (x0:R.term) k'0 e1 ...
        apply (H1 e1)...
        * rewrite hh; subst e0; eapply dec_context_term_next...
        * compute; congruence.

      + eapply ro_val...
        assert (v0 = v).
        * apply (value_to_term_injective v0 v); congruence.
        * subst...

    - assert (H1 := value_to_term_injective _ _ hh); subst; 
      econstructor...

  Qed.


  Lemma refocus_in_redex_self_e :                               forall {k} (r : redex k),
      refocus_in r [.] (d_red r [.]).

  Proof with eauto.
    intros; 
    remember (dec_term r k).

    destruct i;
        assert (hh := dec_term_correct r k);
        rewrite <- Heqi in hh; 
        simpl in hh; try symmetry in hh.

    - apply redex_to_term_injective in hh; subst; constructor...

    - symmetry in Heqi; assert (H0 := dec_term_term_top _ _ Heqi).
      econstructor 3...
      destruct (redex_trivial1 r e t hh) as (v, H1)...

      subst t.
      clear H0 Heqi.
remember (erase_kinds e).
generalize dependent k'.
      induction e0 using (well_founded_ind (wf_search k r)); intros.

      apply refocus_out_to_in.
      remember (dec_context e v); assert (ht := dec_context_correct e v);
      rewrite <- Heqi in ht; symmetry in Heqi.

      destruct i; simpl in ht.

      + rewrite hh in ht.
        apply redex_to_term_injective in ht; subst.
        constructor...

      + econstructor 4...
        rewrite ht in hh.
        destruct (redex_trivial1 r e1 t hh) as (v1, H4)...
        subst t.
        destruct (dec_context_term_next _ _ _ _ Heqi).
        eapply H...
        * congruence.

      + rewrite ht in hh; contradiction (value_redex _ _ hh).


    - contradict hh; apply value_redex.

  Qed.


  Lemma refocus_in_redex_self :      forall {k2} (r : redex k2) {k1} (c : context k1 k2),
      refocus_in r c (d_red r c).

  Proof with eauto.
      intros;
      assert (H := refocus_in_redex_self_e r);
      generalize c.

      (* induction on H *)
      apply refocus_in_Ind with

      (P  := fun k2' t c0 d (_ : refocus_in t c0 d) =>
                 match d with
                 | d_val v      => True
                 | d_red r' c1 => forall (c : context k1 k2),
                                      refocus_in t (c0~+c) (d_red r' (c1~+c))
                 end)
      (P0 := fun k2' v c0 d (_ : refocus_out v c0 d) => 
                 match d with
                 | d_val v      => True
                 | d_red r' c1 => forall (c : context k1 k2),
                                      refocus_out v (c0~+c) (d_red r' (c1~+c))
                 end)
      (r := H);

      intros;
      try destruct d;
      unfold dec in *;
      solve 
      [ auto
      | econstructor;   eauto
      | econstructor 3; eauto
      | econstructor 4; eauto ].
  Qed.



  Lemma refocus_in_under_redex :   
       forall t {k} (r : redex k) {k0 k'} (c : context k0 k) (ec : elem_context_kinded k k'),
       ec:[t] = r -> refocus_in t (ec=:c) (d_red r c).

  Proof.
    intros t k r k0 k' c ec H.
    assert (exists (v : value k'), t = v) as [v H1];
              eauto using redex_trivial1.
    subst.
    apply refocus_out_to_in.
remember (erase_kinds ec).
generalize dependent k'.
    induction e using (well_founded_ind (wf_search k r)); intros.
    remember (dec_context ec v) as D eqn:HeqD; destruct D;
    assert (H2 := dec_context_correct ec v);
    rewrite <- HeqD in H2.
    - constructor 2. 
      assert (r = r0). 
      { apply redex_to_term_injective; congruence. }
      congruence.
    - econstructor 4.
      symmetry; apply HeqD.
      assert (exists (v' : value k'0), t = v') as [v' H3].
      { rewrite H2 in H0; eauto using redex_trivial1... }
      subst t.
      apply refocus_out_to_in.
      apply (H e0).
      + symmetry in HeqD; destruct (dec_context_term_next _ _ _ _ HeqD) as [H3 _].
        congruence. 
      + congruence.
      + trivial.
    - assert ((v0 : term) = r).
      { compute; congruence. }
      exfalso; eauto using (value_redex v0 r).
  Qed.


  Lemma refocus_in_under_value : forall t {k} (v : value k) {k0 k'} (c : context k0 k) 
      (ec : elem_context_kinded k k')  d,
      ec:[t] = v -> refocus_out v c d -> refocus_in t (ec=:c) d.

  Proof.
    intros t k v k0 k' c ec d H H0.
    assert (exists (v : value k'), t = v) as [v0 H2];
              eauto using value_trivial1.
    subst.
    apply refocus_out_to_in.
remember (erase_kinds ec).
generalize dependent k'.
    induction e using (well_founded_ind (wf_search k v)); intros.
    remember (dec_context ec v0) as D eqn:HeqD; destruct D;
    assert (H3 := dec_context_correct ec v0);
    rewrite <- HeqD in H3.
    - assert ((v : term) = r).
      { compute; congruence. }
      exfalso; eauto using (value_redex v r).
    - econstructor 4.
      + symmetry; apply HeqD.
      + assert (exists (v' : value k'0), t = v') as [v' H4].
        { rewrite H3 in H1; eauto using value_trivial1. }
        subst t.
        apply refocus_out_to_in.
        apply (H e0).
        * symmetry in HeqD; destruct (dec_context_term_next _ _ _ _ HeqD) as [H4 _].
          congruence. 
        * congruence.
        * trivial.    
    - assert (v = v1).
      { apply value_to_term_injective; congruence. }
      subst.
      econstructor 3; eauto.
  Qed.


  Lemma refocus_in_plug :                         forall {k1 k2} (c : context k1 k2) {k3}
                                                              {c0 : context k3 k1} {t d},
      refocus_in c[t] c0 d -> refocus_in t (c~+c0) d.

  Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H; clear IHc.
       inversion H; dep_subst.
       assert (hh := dec_term_correct (ec):[t] k2);
       rewrite H3 in hh.

        + auto using refocus_in_under_redex.

        + assert (hh := dec_term_correct (ec):[t] k2);
          rewrite H1 in hh.
          eauto using refocus_in_under_value.

        + assert (hh := dec_term_correct (ec):[t] k2);
          rewrite H1 in hh.

          destruct (search_order_comp_if ec:[t] _ _ _ ec0 ec) as [H3 | [H3 | H3]].
          compute...
          compute...

          * contradiction (dec_term_term_top _ _ H1 ec).
          * destruct (elem_context_det _ _ k5 _ hh _ H3) as (v, H5)...
            subst t1.
            {
                clear H1; 
remember (erase_kinds ec0).
generalize dependent k5.
                induction e using (well_founded_ind (wf_search k2 ec:[t])); intros.

                assert (H5 := refocus_in_to_out _ _ _ H4).
                dependent destruction H5.

 (*               inversion_ccons .*)
                - rewrite hh in H3; 
                  contradiction (dec_context_red_bot _ _ _ _ H1 _ H3).
                - rewrite hh in H3; 
                  contradiction (dec_context_val_bot _ _ _ _ H1 _ H3).
                - assert (ht := dec_context_correct ec0 v).
                  rewrite H1 in ht.
                  rewrite <- hh in ht.
                  destruct (dec_context_term_next _ _ _ _ H1) as (H4', H6).
                  destruct (search_order_comp_if ec:[t] _ _ _ ec2 ec) as [H7|[H7|H7]].

                      compute...
                      compute...
                      assert (H8 := search_order_comp_fi _ _ _ _ _ _ H4'); intuition.
                      assert (H8 := search_order_comp_fi _ _ _ _ _ _ H3); intuition.

                  + contradiction (H6 ec); rewrite <- hh...
                  + destruct (elem_context_det _ _ k2'' _ ht _ H7) as (v1, h4)...
                    subst t0.
                    eapply H0...
                      { congruence. }
                  + subst...
destruct H7.
subst.
assert (ec2 = ec).
apply JMeq_eq.
auto.
subst.
 assert (H8 := elem_plug_injective1 _ _ _ ht).
                    subst...
            }

          * destruct H3; subst.
            assert (ec0 = ec).
            apply JMeq_eq...
            subst...
            assert (H8 := elem_plug_injective1 _ _ _ hh).
            subst...
  Qed.


  Lemma refocus_in_plug_rev :                     forall {k1 k2} (c : context k1 k2) {k3}
                                                                (c0 : context k3 k1) t d,
          refocus_in t (c~+c0) d -> refocus_in c[t] c0 d.

  Proof with eauto.
      induction c; intros; simpl.

      - trivial.

      - apply IHc; clear IHc;
            eauto.

        remember (dec_term ec:[t] k2) as D;
        symmetry in HeqD;
        destruct D;
        assert (DTC2 := dec_term_correct ec:[t] k2);
        rewrite HeqD in DTC2;
        subst.
        + cut (d = d_red r (c~+c0)).
          { intro; subst; constructor; auto. }

          destruct (redex_trivial1 _ _ _ DTC2) as [v ?]; subst t.
          eapply refocus_in_to_out in H.

          clear HeqD.
remember (erase_kinds ec).
generalize dependent k3.
          induction e using (well_founded_ind (wf_search k2 r)); intros.

          dependent destruction H0; dep_subst;
(*          simpl in x; inversion_ccons x;*)
          assert (DCC := dec_context_correct ec v);
          rewrite H0 in DCC.
          * assert (r = r0).
            { apply redex_to_term_injective; congruence. }
            subst.
            constructor...
          * assert ((v0 : term) = r).
            { compute; congruence. }
            exfalso; eauto using (value_redex v0 r).
          * destruct (redex_trivial1 r ec1 t) as [v' ?]; 
                try solve [auto | congruence].
            subst t.
            eapply (H ec1);
            try solve
            [rewrite <- DTC2; destruct (dec_context_term_next _ _ _ _ H0); auto
            | eauto using refocus_in_to_out
            | compute; congruence ].

        + destruct (search_order_comp_if ec:[t] _ _ _ e ec) as [H1 | [H1 | H1]].
              compute...
              compute...
          * contradict (dec_term_term_top _ _ HeqD _ H1).

          * destruct (elem_context_det _ _ k' _   DTC2 _ H1) as (v, H2)...
            subst t0.
            econstructor 3; eauto.
            {
              clear HeqD.
remember (erase_kinds e).
generalize dependent v; generalize dependent k'.

              induction e0 using (well_founded_ind (wf_search k2 ec:[t])); intros.

              apply refocus_out_to_in.
              remember (dec_context e v) as D.
              destruct D;
                  symmetry in HeqD;
                  assert (ht := dec_context_correct e v); 
                  rewrite HeqD in ht.

              - rewrite DTC2 in H1;
                contradiction (dec_context_red_bot _ _ _ _ HeqD _ H1).

              - destruct (dec_context_term_next _ _ _ _ HeqD) as (H3, H4).
                econstructor 4...
                rewrite <- DTC2 in ht.
                destruct (search_order_comp_if ec:[t] _ _ _ e1 ec) as [H5 | [H5 | H5]].
                    compute...
                    compute...

                + rewrite DTC2 in *; 
                  contradiction (H4 ec H1).

                +
                 rewrite DTC2 in *.
                 destruct (elem_context_det _ _ k'0 _ ht _ H5) as (v0, H6)...
                  subst t0.
                  subst.
                  eapply H0...
                + subst.
                destruct H5; subst k'0.
                assert (e1=ec).
                apply JMeq_eq...
                subst.
                  assert (H5 := elem_plug_injective1 _ _ _  ht).
                  subst...

              - rewrite DTC2 in H1;
                contradiction (dec_context_val_bot _ _ _ _ HeqD _ H1).
                }

          * subst.
            destruct H1; subst.
            assert (e = ec).
            apply JMeq_eq...
            subst.
            assert (H5 := elem_plug_injective1 _ _ _ DTC2).
            subst.
            econstructor 3...

        + cut (refocus_out v (c~+c0) d).
          { intro; econstructor; eauto. }

          destruct (value_trivial1 _ _ DTC2) as [v' ?].
          subst t.
          capture_all value @value_to_term.
          eapply refocus_in_to_out in H.

          clear HeqD.
remember (erase_kinds ec).
generalize dependent k3.          
          induction e using (well_founded_ind (wf_search k2 v)); intros.

          assert (DCC := dec_context_correct ec v').
          dependent destruction H0; (*simpl in x; inversion_ccons x;*)
          rewrite H0 in DCC.
          * exfalso.
            assert ((v : term) = r).
            { congruence. }
            eauto using (value_redex v r).
          * replace v1 with v in * by (apply value_to_term_injective; congruence).
            eauto.
          * destruct (@value_trivial1 _ _ ec1 t v) as [v'' ?];
                try solve [eauto using dec_context_next_alive | congruence].
            capture_all value @value_to_term.
            subst t.
            subst.
            eapply (H ec1) with (v':=v'');
            solve 
            [ destruct (dec_context_term_next _ _ _ _ H0); rewrite <- DTC2; eauto 
            | eauto using refocus_in_to_out
            | congruence ].
  Qed.


  Lemma refocus_in_value_self :                                 forall {k} (v : value k),
       refocus_in v [.] (d_val v).

  Proof with auto.
    intros.
    apply refocus_out_to_in.
    constructor...
  Qed.


  Theorem refocus_in_val_eqv_refocus_out :                forall {k2} (v : value k2) {k1}
                                                                   (c : context k1 k2) d,
       refocus_in v c d <-> refocus_out v c d.

  Proof.
    split; [apply refocus_in_to_out | apply refocus_out_to_in].
  Qed.


  Module DPT := RedDecProcEqvDec R.

  Theorem refocus_in_eqv_dec :                    forall t {k1 k2} (c : context k1 k2) d,
      (refocus_in t c d <-> dec c[t] k1 d).

  Proof. eauto 6 using DPT.dec_proc_eqv_dec, refocus_in_correct, 
                       refocus_in_plug, refocus_in_plug_rev,
                       refocus_in_redex_self, refocus_in_value_self. Qed.

End RedRefSem.
