

(*** Interface part ***)

Require Import Entropy
               reduction_semantics
               refocusing_semantics.
Require Export abstract_machine.
Require rewriting_system.





Module Type REF_EVAL_APPLY_MACHINE (Import R' : RED_REF_SEM) <: DET_ABSTRACT_MACHINE.

  Notation ick     := init_ckind.
  Definition term  := term.
  Definition value := value ick.
  Coercion   value_to_term (v : value) := (R.value_to_term v) : term.


  Inductive conf :=
  | c_eval  : term -> forall {k}, context init_ckind k -> conf
  | c_apply : forall {k}, context init_ckind k -> R.value k -> conf.

  Definition configuration := conf.
  Definition load (t : term)           : configuration := c_eval t [.].
  Definition final (c : configuration) : option value := 
      match c with
      | c_apply [.] v => Some v 
      | _             => None
      end.
  Definition decompile (c : configuration) : term :=
      match c with
      | c_eval t c  => c[t]
      | c_apply c v => c[v]
      end.
  Definition is_final c := exists v, final c = Some v.


  Section S1.

  Local Reserved Notation "c1 → c2"                      (no associativity, at level 70).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red :                                        forall t {k} (c : context ick k) r t0,
        dec_term t k = ed_red r -> 
        contract r = Some t0 ->
        c_eval t c → c_eval t0 c

  | t_val :                                           forall t {k} (c : context ick k) v,
        dec_term t k = ed_val v ->
        c_eval t c → c_apply c v

  | t_term :    forall t {k} (c : context ick k) {t0 k'} {ec : elem_context_kinded k k'},
        dec_term t k = ed_dec k' t0 ec ->
        c_eval t c → c_eval t0 (ec=:c)

  | t_cred :     forall {k k'} (ec : elem_context_kinded k k') (c : context ick k) v r t,
        dec_context ec v = ed_red r -> 
        contract r = Some t ->
        c_apply (ec=:c) v → c_eval t c

  | t_cval :      forall {k k'} (ec : elem_context_kinded k k') (c : context ick k) v v0,
        dec_context ec v = ed_val v0 ->
        c_apply (ec=:c) v → c_apply c v0

  | t_cterm :                           forall {k k' k''} (ec : elem_context_kinded k k')
                               (ec0 : elem_context_kinded k k'') (c : context ick k) v t,
        dec_context ec v = ed_dec k'' t ec0 ->
        c_apply (ec=:c) v → c_eval t (ec0=:c)

  where "st1 → st2" := (trans st1 st2).

  End S1.
  Import rewriting_system.
  Definition transition := trans.


  Definition dnext_conf (st : configuration) : option configuration :=
      match st with
      | @c_eval t k c  => 
            match dec_term t k with
            | ed_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v     => Some (c_apply c v)
            | ed_dec _ t ec => Some (c_eval t (ec=:c))
             end
      | c_apply (pcons ec c) v =>
            match dec_context ec v with
            | ed_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v     => Some (c_apply c v)
            | ed_dec _ t ec => Some (c_eval t (ec=:c))
            end
      | c_apply [.] _ => 
            None
      end.
  Definition next_conf (_ : entropy) := dnext_conf.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Axioms
  (final_correct :                                                             forall st,
       final st <> None -> ~exists st', st → st')
  (trans_computable :                                                     forall st1 st2,
       st1 → st2 <-> exists e, next_conf e st1 = Some st2)
  (dnext_is_next :                                                            forall e c,
      next_conf e c = dnext_conf c).


  Class SafeRegion (P : configuration -> Prop) :=
  {
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.

End REF_EVAL_APPLY_MACHINE.


(*

Module Type REF_EVAL_APPLY_MACHINE (R : RED_REF_SEM) <: DET_ABSTRACT_MACHINE.

  Import R ST.

  Declare Module RAW : SLOPPY_REF_EVAL_APPLY_MACHINE R.
  Export RAW.


  Notation   ick   := init_ckind.
  Definition term  := term.
  Definition value := RAW.value.
  Coercion   value_to_term (v : value) := (R.value_to_term v) : term.


  Definition configuration := RAW.configuration.

  Definition load t : configuration := 
      RAW.c_eval t [.].

  Definition final (c : configuration)     : option value := RAW.final c. 
  Definition decompile (c : configuration) : term         := RAW.decompile c.
  Definition transition (st1 st2 : configuration)         := RAW.transition st1 st2.
  Definition is_final c                                   := exists v, final c = Some v.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Definition dnext_conf (st : configuration) : option configuration :=

      match RAW.dnext_conf st                                                      as sto
                                   return RAW.dnext_conf st = sto -> option configuration
      with
      | Some st' => fun H => Some st'
      | None     => fun _ => None
      end eq_refl.

  Definition next_conf (_ : entropy) := dnext_conf.


  Axioms
  (final_correct :                                                             forall st,
       final st <> None -> ~exists st', st → st')
  (trans_computable :                                                     forall st1 st2,
       st1 → st2 <-> exists e, next_conf e st1 = Some st2)
  (*finals_are_vals :                                                        forall st v,
       final st = Some v <-> st = v*)
  (dnext_is_next :                                                            forall e c,
      next_conf e c = dnext_conf c).


  Class SafeRegion (P : configuration -> Prop) :=
  { 
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.

End REF_EVAL_APPLY_MACHINE.

*)

(*
Module Type REF_PUSH_ENTER_MACHINE (R : RED_PE_REF_SEM R) <: DET_ABSTRACT_MACHINE.

  Import R.
  Import PERS.ST.


  Definition term  := term.
  Definition value := value init_ckind.


  Inductive conf : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_fin : forall {k}, R.value k                -> conf.
  Definition configuration := conf.

  Definition c_init t  := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_fin v.
  (*Definition final_of (st : configuration) : option value := 
      match st with 
      | c_fin k v => 
          match is_initial k with
          | left H => match H in _ = k return R.value k -> option value with
                      | eq_refl => fun v => Some v
                      end v
          | _      => None
          end
      | _ => None
      end.
  Axiom final_of_correct : forall c v, final_of c = Some v <-> c_final v = c.*)


  Reserved Notation "c1 → c2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = ed_red r -> 
               contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : R.value k},
               dec_term t k = ed_val v ->
               c_eval t [.](k) → c_fin v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = ed_val v ->
               dec_context ec k2 v = ed_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = ed_val v ->
               dec_context ec k2 v = ed_dec t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = ed_dec t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.
  Hint Unfold transition.

  Axiom final_correct : forall v st, ~ c_final v → st.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | ed_red r => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v => match c in context _ k2 
                              return R.value k2 -> option configuration with 
                          | [.]          => fun _ => Some (c_fin v)
                          | ccons ec k c => fun v => 
                                match dec_context ec k v with
                                | ed_red r       => option_map (fun t' => c_eval t' c)
                                                               (contract r)
                                | ed_dec t' ec' => Some (c_eval t' (ec'=:c))
                                | _              => None
                                end
                          end v
            | ed_dec t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | _ => None
      end.


  Axiom next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

End REF_PUSH_ENTER_MACHINE.*)






(*** Implementation part ***)


Require Import Util
               reduction_languages_facts.


Module RefEvalApplyMachine (Import R' : RED_REF_SEM) <: REF_EVAL_APPLY_MACHINE R'.

  Include RED_LANG_Facts R'.


  Notation   ick   := init_ckind.
  Definition term  := term.
  Definition value := value ick.
  Coercion   value_to_term (v : value) := (R.value_to_term v) : term.


  Inductive conf : Type :=
  | c_eval  : term -> forall {k}, context init_ckind k -> conf
  | c_apply : forall {k}, context init_ckind k -> R.value k -> conf.
  Definition configuration := conf.


  Definition load t                    : configuration := c_eval t [.].
  
  Definition value_to_conf (v : value) : configuration := 
      c_apply [.] v.
  Coercion value_to_conf : value >-> configuration.

  Definition final (c : configuration) : option value := 
      match c with
      | c_apply [.] v => Some v 
      | _             => None
      end.
  Definition decompile (c : configuration) : term :=
      match c with
      | c_eval t c  => c[t]
      | c_apply c v => c[v]
      end.
  Definition is_final c := exists v, final c = Some v.


  Section S1.

  Local Reserved Notation "c1 → c2" (no associativity, at level 70).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red :                                        forall t {k} (c : context ick k) r t0,
        dec_term t k = ed_red r -> 
        contract r = Some t0 ->
        c_eval t c → c_eval t0 c

  | t_val :                                           forall t {k} (c : context ick k) v,
        dec_term t k = ed_val v ->
        c_eval t c → c_apply c v

  | t_term :    forall t {k} (c : context ick k) {t0 k'} {ec : elem_context_kinded k k'},
        dec_term t k = ed_dec k' t0 ec ->
        c_eval t c → c_eval t0 (ec=:c)

  | t_cred :     forall {k k'} (ec : elem_context_kinded k k') (c : context ick k) v r t,
        dec_context ec v = ed_red r -> 
        contract r = Some t ->
        c_apply (ec=:c) v → c_eval t c

  | t_cval :      forall {k k'} (ec : elem_context_kinded k k') (c : context ick k) v v0,
        dec_context ec v = ed_val v0 ->
        c_apply (ec=:c) v → c_apply c v0

  | t_cterm :                           forall {k k' k''} (ec : elem_context_kinded k k')
                               (ec0 : elem_context_kinded k k'') (c : context ick k) v t,
        dec_context ec v = ed_dec k'' t ec0 ->
        c_apply (ec=:c) v → c_eval t (ec0=:c)

  where "st1 → st2" := (trans st1 st2).

  End S1.
  Import rewriting_system.
  Definition transition := trans.

  Definition dnext_conf (st : configuration) : option configuration :=
      match st with
      | @c_eval t k c  => 
            match dec_term t k with
            | ed_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v     => Some (c_apply c v)
            | ed_dec _ t ec => Some (c_eval t (ec=:c))
             end
      | c_apply (pcons ec c) v =>
            match dec_context ec v with
            | ed_red r     => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v     => Some (c_apply c v)
            | ed_dec _ t ec => Some (c_eval t (ec=:c))
            end
      | c_apply [.] _ => 
            None
      end.

  Definition next_conf (_ : entropy) := dnext_conf.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Lemma final_correct :                                                         forall c,
       final c <> None -> ~exists c', c → c'.

  Proof.
    intros c H [c' H0].
    inversion H0; subst;
        simpl in H;
    congruence.
  Qed.
  
  Lemma trans_computable0 :                                                 forall c1 c2,
       c1 → c2 <-> dnext_conf c1 = Some c2.

  Proof.
    intros c1 c2; split; intro H.

  (* -> *) {
      destruct H;
          simpl;
          match goal with H : @eq (elem_dec _) _ _ |- _ => rewrite H end;
      solve 
      [ eauto 
      | rewrite H0; eauto].
  }

  (* <- *) {
      destruct c1; simpl in H.
      - remember (dec_term t k) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_red; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_term; auto.
        + inversion H; subst.
          apply t_val; auto.
      - destruct c; autof.
        remember (dec_context ec v) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_cred; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_cterm; auto.
        + inversion H; subst.
          apply t_cval; auto.
  }
  Qed.


  Lemma trans_computable :                                                  forall c1 c2,
       c1 → c2 <-> exists e, next_conf e c1 = Some c2.

  Proof with auto.
    intuition.
    - destruct (draw_fin_correct 1 Fin.F1) as [ent _].
      exists ent.
      apply trans_computable0...
    - destruct H as [ent H].
      apply trans_computable0...
  Qed.

  Lemma finals_are_vals :                                                    forall st v,
      final st = Some v <-> st = v.

  Proof.
    intros st v.
    destruct st as [? ? ? | ? c ?]; simpl.
    - intuition.
    - destruct c.
      + split; intro H;
            inversion H; dep_subst;
            unfold value_to_conf;
        solve [try apply (f_equal (submember _ _)); auto].
      + intuition.
  Qed.
  
  Lemma dnext_is_next :                                                      forall e c,
      next_conf e c = dnext_conf c.

  Proof.
    auto.
  Qed.


  Class SafeRegion (P : configuration -> Prop) :=
  { 
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.

End RefEvalApplyMachine.



(*

Module RefEvalApplyMachine (R : RED_REF_SEM) <: REF_EVAL_APPLY_MACHINE R.

  Module RF := RED_LANG_Facts R.
  Import R RF ST.


  Module RAW := SloppyRefEvalApplyMachine R.
  Export RAW.


  Notation   ick   := init_ckind.
  Definition term  := term.
  Definition value := RAW.value.
  Coercion   value_to_term (v : value) := (R.value_to_term v) : term.
 

  Definition configuration := RAW.configuration.

  Coercion conf_to_raw (st : configuration) := st.

  Definition load t : configuration := 
      RAW.c_eval t [.].

  Definition value_to_conf (v : value) : configuration := 
      RAW.c_apply [.] v.
  Coercion value_to_conf : value >-> configuration.

  Definition final (c : configuration) : option value := RAW.final c. 
  Definition decompile (c : configuration) : term     := RAW.decompile c.
  Definition transition (st1 st2 : configuration)     := RAW.transition st1 st2.
  Definition is_final c := exists v, final c = Some v.

  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Definition dnext_conf (st : configuration) : option configuration :=

      match RAW.dnext_conf st                                                      as sto
                                   return RAW.dnext_conf st = sto -> option configuration
      with
      | Some st' => fun H => Some st'
      | None     => fun _ => None
      end eq_refl.

  Definition next_conf (_ : entropy) := dnext_conf.


  Lemma final_correct :                                                         forall c,
      final c <> None -> ~exists c', c → c'.

  Proof.
    intros c H [c' H0].
    destruct c, c';
        compute in H0;
        inversion H0; dep_subst;
        compute in H;
    congruence.
  Qed.


  Lemma RAW_trans_computable0 :                           forall st1 st2 : configuration,
      st1 → st2 <-> RAW.dnext_conf st1 = Some (st2 : RAW.configuration).

  Proof.
    destruct st1, st2;
    apply RAW.trans_computable0.
  Qed.



  Lemma trans_computable0 :                                                 forall c1 c2,
      c1 → c2 <-> dnext_conf c1 = Some c2.

  Proof. 
    intros c1 c2. 

    rewrite (RAW_trans_computable0 c1 c2).
    unfold dnext_conf.
    generalize (eq_refl : RAW.dnext_conf c1 = RAW.dnext_conf c1) as H.
    intro H.
    set (RAW.dnext_conf c1) as sto in H at 2 |- * at 2.
    destruct sto.
    - destruct c as [t k c | k c v];
          rewrite H at 1; destruct c2;
          split; intro H0; 
          inversion H0; dep_subst;
      solve 
      [ repeat f_equal; apply (f_equal (submember _ _)); apply witness_unique ].
    - split; congruence.
  Qed.


  Lemma trans_computable :                                                  forall c1 c2,
      c1 → c2 <-> exists e, next_conf e c1 = Some c2.

  Proof with auto.
    intros c1 c2; split; intro H.
    - destruct entropy_exists as [e _].
      exists e.
      apply trans_computable0...
    - destruct H.
      apply trans_computable0...
  Qed.


  Lemma finals_are_vals :                                                    forall st v,
      final st = Some v <-> st = v.

  Proof.
    intros st v.
    destruct st as [? ? ? | ? c ?]; simpl.
    - intuition.
    - destruct c.
      + split; intro H;
            inversion H; dep_subst;
            unfold value_to_conf;
        solve [try apply (f_equal (submember _ _)); auto].
      + intuition.
  Qed.


  Lemma dnext_is_next :                                                      forall e c,
      next_conf e c = dnext_conf c.

  Proof.
    auto.
  Qed.


  Class SafeRegion (P : configuration -> Prop) :=
  { 
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.

End RefEvalApplyMachine.

*)


(*Module RefPushEnterMachine (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                                 <: REF_PUSH_ENTER_MACHINE R PERS.

  Import R.
  Import PERS.ST.


  Definition term  := term.
  Definition value := value init_ckind.


  Inductive conf : Set :=
  | c_eval : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_fin  : forall {k}, R.value k                 -> conf.
  Definition configuration := conf.

  Definition c_init t            := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_fin v.


  Reserved Notation "c1 → c2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = ed_red r -> 
               contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : R.value k},
               dec_term t k = ed_val v ->
               c_eval t [.](k) → c_fin v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = ed_val v ->
               dec_context ec k2 v = ed_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = ed_val v ->
               dec_context ec k2 v = ed_dec t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = ed_dec t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.
  Hint Unfold transition.


  Lemma final_correct : forall v st, ~ c_final v → st.
  Proof. inversion 1. Qed.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).


  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | ed_red r => option_map (fun t' => c_eval t' c) (contract r)
            | ed_val v => match c in context _ k2 
                              return R.value k2 -> option configuration with 
                          | [.]          => fun _ => Some (c_fin v)
                          | ccons ec k c => fun v => 
                                match dec_context ec k v with
                                | ed_red r       => option_map (fun t' => c_eval t' c)
                                                               (contract r)
                                | ed_dec t' ec' => Some (c_eval t' (ec'=:c))
                                | _              => None
                                end
                          end v
            | ed_dec t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | _ => None
      end.


  Lemma next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

  Proof.
    intros c1 c2; split; intro H.

  (* -> *) {
      destruct c1; simpl in H.
      - remember (dec_term t k2) as dc.
        destruct dc.
        + remember (contract r) as opt.
          destruct opt.
          * inversion H; subst.
            eapply t_red; eauto.
          * inversion H.
        + inversion H; subst.
          apply t_rec; auto.
        + destruct c.
          * inversion H; subst.
            apply t_cval; auto.
          * remember (dec_context ec k2 v) as dc.
            destruct dc;
            inversion H.
            { remember (contract r) as opt.
              destruct opt;
              inversion H; subst.
              eapply t_cred; eauto. }
            { eapply t_crec; eauto. }
        + inversion H.
      - inversion H. 
  }

  (* <- *) {
      destruct H;
          simpl;
          match goal with H : @eq (elem_dec _) _ _ |- _ => rewrite H end;
      try solve 
      [ auto 
      | rewrite H0; try rewrite H1; auto].
  }
  Qed.

End RefPushEnterMachine.*)
