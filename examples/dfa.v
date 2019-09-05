(* Deterministic finite automaton expressed by generalized refocusing *)

Require Import List
               Program
               Util
               RelationClasses
               refocusing_semantics.

Module Type DFA.
  Parameters
  (state : Set)
  (alphabet : Set)
  (transition : alphabet -> state -> state)
  (initial_state : state).
End DFA.

Module DFA_Notions (Import D : DFA).
  Inductive transforms : list alphabet -> state -> state -> Prop :=
  | transforms_nil  : forall s, transforms [] s s
  | transforms_cons : forall l ls s s' s'',
      transition l s = s' ->
      transforms ls s' s'' ->
      transforms (l::ls) s s''.

  Lemma transforms_deterministic : forall t s s' s'',
    transforms t s s' -> transforms t s s'' -> s' = s''.
  Proof.
    induction t;
    intros s s' s'' H H0; inversion H; inversion H0; subst.
    { reflexivity. }
    eapply IHt; eassumption.
  Qed.
End DFA_Notions.


Module DFA_PreRefSem (Import D : DFA) <: PRE_REF_SEM.
  Include DFA_Notions D.

  Definition term := list alphabet.
  Hint Unfold term.

  Definition ckind : Type := state.
  Hint Unfold ckind.

  Definition init_ckind : ckind :=  initial_state.

  Inductive val : ckind -> Type :=
  | Value : forall {k:ckind} (t:term) (s:state),
      transforms t k s -> val k.

  Definition value := val.
  Hint Unfold value.

  Definition value_to_term {k} (v : value k) : term :=
    match v with Value t _ _ => t end.

  Inductive red : ckind -> Type :=.
  Definition redex := red.
  Hint Unfold redex.

  Definition redex_to_term {k} (r : redex k) : term :=
    match r with end.

  Definition contract {k} (r : redex k) : option term :=
    match r with end.

  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Proof.
    intros k [? t b H] v' H0.
    dependent destruction v'.
    simpl in H0. subst.
    assert (H0 := transforms_deterministic _ _ _ _ H t1). subst.
    rewrite (proof_irrelevance _ H t1).
    reflexivity.
  Qed.

  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.
  Proof. intros _ []. Qed.

  Inductive eck : ckind -> ckind -> Type :=
  | letter : forall l k k', transition l k = k' -> eck k k'.

  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
    match ec with letter l _ _ _ => l::t end.

  Include RED_SEM_BASE_Notions.

  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.
  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    inversion H; trivial.
  Qed.

  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.

  Definition wf_subterm_order : well_founded subterm_order
    := wf_clos_trans_l _ _ wf_immediate_subterm.

  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                             exists (v' : value k2), t = v'.
  Proof.
    intros k1 k2 ec ls v H0.
    destruct ec, v.
    simpl in H0. subst.
    inversion t0. subst.
    exists (Value _ _ H4).
    reflexivity.
  Qed.

  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof. intros _ _ []. Qed.

  Lemma redex_trivial1 : forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.
  Proof. intros _ _ []. Qed.

End DFA_PreRefSem.

Module Type DFA_PreRefSem_Type (Import D : DFA).
  Include DFA_PreRefSem D.
End DFA_PreRefSem_Type.

Module DFA_Strategy (Import D : DFA) (Import DPRS : DFA_PreRefSem_Type D) <: REF_STRATEGY DPRS.
  Include RED_STRATEGY_STEP_Notions DPRS.

  Definition dec_term (t : term) (k : ckind) : elem_dec k :=
    match t with
    | []    => ed_val (Value nil k (transforms_nil _))
    | l::ls => ed_dec (transition l k) ls (letter l k _ (eq_refl))
    end.

  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).
  Proof. intros [|] k; reflexivity. Qed.

  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec with
    | letter l _ _ e => (fun v =>
        match v with
        | @Value _ t s H => (fun e =>
            ed_val (Value (l::t) s (transforms_cons _ _ _ _ _ e H)))
        end e)
    end v.

  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).
  Proof. intros ? ? []. destruct v. reflexivity. Qed.

  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop := False.

  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).

  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
                                     (no associativity, at level 70, ec1, t at level 69).

  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. intros ? ? ?. apply Acc_intro. intros _ []. Qed.

  Lemma search_order_trans : forall k t, Transitive (search_order k t).
  Proof. intros ? ? ? ? ? []. Qed.

  Lemma search_order_comp_fi :
      forall t k k' k'' (ec0 : elem_context_kinded k k')
                        (ec1 : elem_context_kinded k k''),
          k, t |~ ec0 << ec1 ->
              immediate_ec ec0 t /\ immediate_ec ec1 t.
  Proof. intros ? ? ? ? ? ? []. Qed.

  Lemma search_order_comp_if :   forall t k k' k'' (ec0 : elem_context_kinded k k')
      (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1).
  Proof.
    intros t k k' k'' [] ? [] [].
    right. right.
    destruct ec1.
    simpl in *. subst.
    inversion H0. subst.
    auto.
  Qed.

  Definition so_maximal {k} (ec : elem_context_in k) t :=
       forall (ec' : elem_context_in k), ~ t |~ ec << ec'.
  Definition so_minimal {k} (ec : elem_context_in k) t :=
       forall (ec' : elem_context_in k), ~ t |~ ec' << ec.
  Definition so_predecessor                                                           {k}
      (ec0 : elem_context_in k) (ec1 : elem_context_in k) t :=

      (*1*) t |~ ec0 << ec1 /\
      (*2*)                                              forall (ec : elem_context_in k),
            t |~ ec << ec1  ->  ~ t |~ ec0 << ec.
  Hint Unfold so_maximal so_minimal so_predecessor.

  Lemma dec_term_term_top : forall {k k'} t t' (ec : elem_context_kinded k k'),
          dec_term t k = ed_dec _ t' ec -> so_maximal ec t.
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma dec_context_val_bot : forall {k k'} (v : value k') {v' : value k}
      (ec : elem_context_kinded k k'),
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
  Proof. intros ? ? ? ? ? ? ? []. Qed.

  Lemma dec_context_term_next :                        forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].
  Proof.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0, v.
    simpl in H.
    discriminate.
  Qed.

  Lemma elem_context_det :         forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].
  Proof. intros ? ? ? t ec0 ec1 []. Qed.

End DFA_Strategy.

Module Parity_DFA <: DFA.
  Definition state := bool.
  Definition alphabet := bool.
  Definition transition := xorb.
  Definition initial_state := true.
End Parity_DFA.

Module Parity_PreRefSem := DFA_PreRefSem Parity_DFA.
Module Parity_Strategy := DFA_Strategy Parity_DFA Parity_PreRefSem.
Module Parity_RefSem := RedRefSem Parity_PreRefSem Parity_Strategy.

Require Import refocusing_machine.

Module Parity_EAM := RefEvalApplyMachine Parity_RefSem.

Import Parity_PreRefSem.

Import Parity_EAM.

Require Import abstract_machine_facts.
Module Parity_sim := DetAbstractMachine_Sim Parity_EAM.

Definition t := [true; false; true; true].

Compute Parity_sim.list_configurations t 10.
