Require Import Coq.Logic.ConstructiveEpsilon
               Util
               Entropy
               rewriting_system
               abstract_machine.



Module ABSTRACT_MACHINE_Facts (AM : ABSTRACT_MACHINE).

  Import AM.


  Lemma preservation_refl_trans :                       forall {P} `{SafeRegion P} c1 c2,
      P c1  ->  c1 →* c2  ->  P c2.

  Proof with auto.
    intros ? ? c1 c2 H1 H2.
    induction H2.
    - auto.
    - apply preservation in H0;
      auto.
  Qed.


  Lemma progress_refl_trans :                           forall {P} `{SafeRegion P} c1 c2,
      P c1  ->  c1 →* c2  ->  is_final c2 \/ exists c3, c2 → c3.

  Proof with auto.
    intros ? ? c1 c2 H1 H2.
    apply preservation_refl_trans in H2...
    apply progress...
  Qed.

End ABSTRACT_MACHINE_Facts.




Module DET_ABSTRACT_MACHINE_Facts (AM : DET_ABSTRACT_MACHINE).

  Import AM.


  Lemma trans_det :                                                      forall c1 c2 c3,
      c1 → c2  ->  c1 → c3  ->  c2 = c3.

  Proof.
    intros ? ? ? H H0.
    compute in H, H0.
    rewrite trans_computable in *.
    destruct H as [? H], H0 as [? H0].
    rewrite dnext_is_next in *.
    congruence.
  Qed.


  Lemma dnext_correct :                                                     forall c1 c2,
      c1 → c2 <-> dnext_conf c1 = Some c2.

  Proof.
    intros.
    compute -[iff].
    rewrite trans_computable.
    split; intro H.
    - destruct H as [e ?].
      rewrite <- (dnext_is_next e).
      auto.
    - destruct entropy_exists as [e _].
      exists e.
      rewrite (dnext_is_next e).
      auto.
  Qed.

End DET_ABSTRACT_MACHINE_Facts.




Module DetAbstractMachine_Sim (AM : DET_ABSTRACT_MACHINE).

  Module AMF := DET_ABSTRACT_MACHINE_Facts AM.
  Import AM AMF.

  Definition n_steps (c : configuration) (n : nat) : option configuration :=
    option_n_binds n dnext_conf c.

  Lemma n_steps_correct :                                                 forall c1 n c2,
      n_steps c1 n = Some c2  ->  c1 →* c2.

  Proof with auto.
    intros c1 n c2; revert c1.

    induction n; 
        intros c1 H.

    - compute in H.
      inversion H; subst.
      constructor.

    - remember (dnext_conf c1) as c1'.
      destruct c1';
          unfold n_steps in H; simpl in H;
          rewrite <- Heqc1' in *.
      + constructor 2 with c.
        * apply dnext_correct...
        * auto.
      + discriminate.
  Qed.


  Lemma n_steps_complete :                                                  forall c1 c2,
      c1 →* c2   ->  exists n, n_steps c1 n = Some c2.

  Proof.
    induction 1.
    - exists 0; simpl.
      auto.
    - destruct IHclos_refl_trans_1n as (n, ?).
      apply dnext_correct in H.
      eexists (S n).
      cbn.
      rewrite H.
      auto.
  Qed.


(* BEGINE Hell

  Axiom conf_eq_dec : forall c1 c2 : configuration, {c1 = c2} + {c1 <> c2}.

  Definition steps_count c1 c2 (H : c1 →+ c2) : nat.
    refine (
     (fix aux c1 c2 (H : c1 →+ c2) {struct H} :=
      match next_conf c1 as c' return next_conf c1 = c' -> nat with
      | None    => fun _ => _
      | Some c' => fun G => if conf_eq_dec c' c2 then 1
                            else S (aux c' c2 _)
      end eq_refl)
      c1 c2 H).
  - destruct H0 as [? ? H0 | ? ? ? H0 ?];
        apply next_correct in H0;
        rewrite H0 in G; inversion G; subst;
    solve [tauto].
  - contradict _H.
    destruct H0 as [? ? H0 | ? ? ? H0 ?];
        apply next_correct in H0;
        rewrite H0;
    solve [discriminate].
  Defined.


  Require Import Program.
(*
  Lemma L : forall c1 c2 (H : c1 →+ c2),
                steps_count c1 c2 H <> 0.
  Proof.
    intros c1 c2 H.
    destruct H.
    simpl.
    remember (next_conf c1).
    dependent destruction (next_conf c1).
*)
  Lemma steps_count_correct : 
      forall c1 c2 (H : c1 →+ c2), n_steps c1 (steps_count c1 c2 H) = Some c2.

  Proof.
    intros c1 c2 H.
    remember (steps_count c1 c2 H) as n.
    induction n.
    destruct H as [? ? H | ? ? ? H H'];
        assert (HH := H);
        apply next_correct in HH.
    + simpl in Heqn.
      rewrite HH in Heqn.
    
    remember (next_conf c1) as c'.
    destruct c

END Hell *)

  (* List of numbered configurations while executing the machine on configuration c
     for n steps and starting the numbering from i  *)
  Fixpoint list_configs c n i :=
   match n with
   | 0 => nil
   | S n' =>  match c with
              | None => nil
              | Some c' => cons (i,c')  (list_configs (n_steps c' 1) n' (S i))
              end
   end.


  (* List of numbered configurations while executing the machine for n steps on term t *)
  Fixpoint list_configurations t n := list_configs (Some (load t)) n 1.




  Definition O_witness_from_ex : forall (P : nat -> Prop),
    (exists n, P n) -> before_witness P 0 :=
    fun P nH => match nH with
    | ex_intro _ n H => O_witness P n (stop P n H)
    end.

  Definition n_steps_terminate c n := exists c', n_steps c n = Some c' /\ dnext_conf c' = None.

  Definition n_steps_terminate_dec :
    forall c n c', n_steps c n = c' -> {n_steps_terminate c n}+{~n_steps_terminate c n}.
  Proof.
    intros ? ? [c'|] ?; try(destruct (dnext_conf c') eqn:H').
    1,3: right; intros [? [? ?]]; congruence.
    left. exists c'. auto.
  Qed.

  Fixpoint last_configuration_aux c m c' (H : n_steps c m = c')
    (b : before_witness (n_steps_terminate c) m) :
    {n & {c'' | n_steps_terminate c n /\ n_steps c n = c''}}.
  refine (match n_steps_terminate_dec c m c' H with
  | left yes => existT _ m (exist _ c' (conj yes H))
  | right no => last_configuration_aux c (S m)
                (option_bind c' dnext_conf) _
                (inv_before_witness _ m b no)
  end).
  + cbn.
    rewrite option_n_binds_assoc, <- H.
    reflexivity.
  Defined.

  Definition last_configuration c (H : exists n, n_steps_terminate c n) :
    nat * configuration.
  Proof.
    destruct (last_configuration_aux c 0 (Some c) eq_refl (O_witness_from_ex _ H))
      as [n [[c'|] [H' ?]]].
    + exact (n, c').
    + exfalso.
      destruct H' as [? [? _]].
      congruence.
  Defined.

  Definition eval (t : term) (H : exists n, n_steps_terminate (load t) n) : option value :=
    match last_configuration (load t) H with
    | (_, c) => final c
    end.

End DetAbstractMachine_Sim.



(*
Module Type AM_INIT_SAFE (AM : ABSTRACT_MACHINE) (S : AM_SAFE_REGION AM).

  Import AM S.

  Axiom init_safe : forall t, safe (c_init t).

End AM_INIT_SAFE.




Module AM_ProgressFromSafety (AM : ABSTRACT_MACHINE) (S : AM_SAFE_REGION AM)
                             (IS : AM_INIT_SAFE AM S) : AM_PROGRESS AM.

  Import AM.

  Module SRF := AM_SafeRegion_Facts AM S.


  Lemma progress : forall t c, c_init t →* c ->
                       (exists v, c = c_final v) \/ (exists c', c → c').

  Proof.
    intros t c H.
    apply S.progress.
    destruct H.
    - subst; apply IS.init_safe.
    - eapply SRF.preservation_trans;
      eauto using IS.init_safe.
  Qed.

End AM_ProgressFromSafety.*)

