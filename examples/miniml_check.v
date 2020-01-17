Require Import Program
               Entropy
               Util
               rewriting_system
               miniml
               abstract_machine
               reduction_semantics
               reduction_languages_facts.




Module MiniML_HandDecProc.

  Module RF := RED_LANG_Facts MiniML_PreRefSem.
  Import MiniML_PreRefSem RF.

  Inductive dec_proc' : term -> context' -> decomp' -> Prop :=

  | d_z   : forall c d, decctx_proc' vZ c d             -> dec_proc' Z c d

  | d_s   : forall t c d, dec_proc' t (s_c =: c) d      -> dec_proc' (S t) c d

  | d_case: forall t ez x es c d, 
              dec_proc' t (case_c ez x es =: c) d       -> dec_proc' (Case t ez x es) c d

  | d_var : forall x c d, decctx_proc' (vVar x) c d     -> dec_proc' (Var x) c d

  | d_lam : forall x t c d, decctx_proc' (vLam x t) c d -> dec_proc' (Lam x t) c d

  | d_app : forall t1 t2 c d, 
              dec_proc' t1 (ap_r t2 =: c) d             -> dec_proc' (App t1 t2) c d

  | d_let : forall x t e c d, 
              dec_proc' t (let_c x e =: c) d            -> dec_proc' (Letv x t e) c d

  | d_fix : forall x t c, 
              dec_proc' (Fix x t) c (d_red (rFix x t) c)

  | d_pair: forall t1 t2 c d, 
              dec_proc' t1 (pair_r t2 =: c) d           -> dec_proc' (Pair t1 t2) c d

  | d_fst : forall t c d, dec_proc' t (fst_c =: c) d    -> dec_proc' (Fst t) c d

  | d_snd : forall t c d, dec_proc' t (snd_c =: c) d    -> dec_proc' (Snd t) c d


  with decctx_proc' : value' -> context' -> decomp' -> Prop :=

  | dc_em : forall v,
              decctx_proc' v [.] (d_val v)

  | dc_s  : forall v c d, decctx_proc' (vS v) c d -> decctx_proc' v (s_c =: c) d

  | dc_cs : forall v x ez es (c : context'),
              decctx_proc' v (case_c ez x es =: c) (d_red (rCase v ez x es) c)

  | dc_apr: forall v t (c : context') d, 
              dec_proc' t (ap_l v =: c) d         -> decctx_proc' v (ap_r t =: c) d

  | dc_apl: forall v v0 (c : context'),
              decctx_proc' v (ap_l v0 =: c) (d_red (rApp v0 v) c)

  | dc_let: forall v x e (c : context'),
              decctx_proc' v (let_c x e =: c) (d_red (rLet x v e) c)

  | dc_p_r: forall t v (c : context') d, 
              dec_proc' t (pair_l v =: c) d       -> decctx_proc' v (pair_r t =: c) d

  | dc_p_l: forall v v0 c d, 
              decctx_proc' (vPair v0 v) c d       -> decctx_proc' v (pair_l v0 =: c) d

  | dc_fst: forall v (c : context'), 
              decctx_proc' v (fst_c =: c) (d_red (rFst v) c)

  | dc_snd: forall v (c : context'), 
              decctx_proc' v (snd_c =: c) (d_red (rSnd v) c).


  Definition dec_proc : 
      term -> forall {k1 k2 : ckind}, context k1 k2 -> decomp k1 -> Prop 

      := fun t => ů ů(dec_proc' t).

  Definition decctx_proc : 
      forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop 

      := ů(fun v => ů(decctx_proc' v)).

  Scheme dec_proc_Ind    := Induction for dec_proc'    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc' Sort Prop.


  Lemma dec_val_self : forall (v : value') c d, dec_proc' v c d <-> decctx_proc' v c d.
  Proof.
    induction v;
        intros c d; split; intro H;
        inversion H; dep_subst; 

    solve
    [ auto

    | constructor; auto

    | match goal with H : _ |- _ => 
      apply IHv in H;
      inversion H1; dep_subst;
      solve [ auto ]
      end

    | match goal with H : _ |- _ => 
      apply IHv1 in H;
      inversion H; dep_subst;
      match goal with H : _ |- _ => 
      apply IHv2 in H;
      inversion H; dep_subst;
      solve [ auto ]
      end end

    | constructor; fold (@value_to_term ()); 
      apply IHv; 
      constructor;
      auto

    | constructor; fold (@value_to_term ());
      apply IHv1; constructor;
      apply IHv2; constructor;
      auto ].
  Qed.


  Module RS := MiniML_RefSem.


  Hint Constructors RS.refocus_in RS.refocus_out dec_proc' decctx_proc'.
  Hint Transparent MiniML_Strategy.dec_term MiniML_Strategy.dec_context.

  Theorem dec_proc_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      dec_proc t c d <-> RS.refocus_in t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) {
    destruct k1, k2.
    induction H using dec_proc_Ind with
    (P0 := fun v c d _ => RS.refocus_out v c d); eauto;
    match goal with c : RS.context _ ?k |- RS.refocus_out _ (?ec =: c) _ =>
    solve
    [ eapply (RS.ro_red ec c); eauto
    | eapply (RS.ro_val ec c); eauto
    | eapply (RS.ro_step ec c); eauto ]
    end.
  }

  (* <- *) {
    induction H using RS.refocus_in_Ind with
    (P0 := fun _ v c d _ => decctx_proc v c d);
    try match goal with
    | H : RS.dec_term ?t ?k = ?dc     |- _ => destruct t, k2;
                                              try match dc with
                                              | RS.ed_dec _ _ ?ec => destruct ec
                                              end;
                                              inversion H; subst

    | H : RS.dec_context ?ec ?v = ?dc |- _ => destruct ec, k2;
                                              try match dc with
                                              | RS.ed_dec _ _ ?ec0 => destruct ec0
                                              end;
                                              dependent_destruction2 v;
                                              inversion H; subst
    end;
    destruct_all ckind; simpl; eauto.
  }
  Qed.


  Theorem decctx_proc_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d <-> RS.refocus_out v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    destruct k1, k2.
    induction H using decctx_proc_Ind with
    (P := fun t c d _ => RS.refocus_in t c d); eauto;
    match goal with c : RS.context _ ?k |- RS.refocus_out _ (?ec =: c) _ => 
    solve
    [ eapply (RS.ro_red ec c); eauto
    | eapply (RS.ro_val ec c); eauto
    | eapply (RS.ro_step ec c); eauto ]
    end.
  }

  (* <- *) {
    induction H using RS.refocus_out_Ind with
    (P := fun _ t c d _ => dec_proc t c d);
    try match goal with
    | H : RS.dec_term ?t ?k = ?dc     |- _ => destruct t, k2;
                                              try match dc with
                                              | RS.ed_dec _ _ ?ec0 => destruct ec0
                                              end;
                                              inversion H; subst
    | H : RS.dec_context ?ec ?v = ?dc |- _ => destruct ec, k2;
                                              dependent_destruction2 v;
                                              try match dc with
                                              | RS.ed_dec _ _ ?ec0 => destruct ec0
                                              end;
                                              inversion H; subst
    end; 
    destruct_all ckind; simpl; eauto.
  }
  Qed.

End MiniML_HandDecProc.




Module MiniML_HandMachine <: ABSTRACT_MACHINE.

  Import MiniML_EAM MiniML_PreRefSem.


  Notation "[$ t $]"         := (load t)                                 (t at level 99).
  Notation "[: v :]"         := (value_to_conf v)                        (v at level 99).
  Notation "[$ t , c $]"     := (c_eval t c)                          (t, c at level 99).
  Notation "[: c , v :]"     := (c_apply c v)                         (c, v at level 99).

  Definition dnext_conf (st : configuration) : option configuration :=
      match st with
      | [$ Z, c $]               => Some [: c,  vZ :]
      | [$ S t, c $]             => Some [$ t,  s_c =: c : context _ () $]
      | [$ Var x, c $]           => Some [: c,  vVar x :]
      | [$ Lam x t, c $]         => Some [: c,  vLam x t :]
      | [$ App t1 t2, c $]       => Some [$ t1, ap_r t2 =: c : context _ () $]
      | [$ Case t ez x es, c $]  => Some [$ t,  case_c ez x es =: c : context _ () $]
      | [$ Fix x t, c $]         => Some [$ subst x (Fix x t) t, c $]
      | [$ Letv x t1 t2, c $]    => Some [$ t1, let_c x t2 =: c : context _ () $]
      | [$ Pair t1 t2, c $]      => Some [$ t1, pair_r t2 =: c : context _ () $]
      | [$ Fst t, c $]           => Some [$ t, fst_c =: c : context _ () $]
      | [$ Snd t, c $]           => Some [$ t, snd_c =: c : context _ () $]

      | [: (s_c =: c), v :]               => Some [: c, vS v :]
      | [: (ap_r t =: c), v :]            => Some [$ t, ap_l v =: c : context _ () $]
      | [: (ap_l (vLam x t) =: c), v2 :]  => Some [$ subst x (v2 : term) t, c $]
      | [: (case_c ez x es =: c), vZ :]   => Some [$ ez, c $]
      | [: (case_c ez x es =: c), vS v :] => Some [$ subst x (v : term) es, c $]
      | [: (let_c x e =: c), v :]         => Some [$ subst x (v : term) e, c $]
      | [: (pair_r t =: c), v :]          => Some [$ t, pair_l v =: c : context _ () $]
      | [: (pair_l v1 =: c), v2 :]        => Some [: c, vPair v1 v2 :]
      | [: (fst_c =: c), vPair v1 _ :]    => Some [$ v1 : term, c $]
      | [: (snd_c =: c), vPair _ v2 :]    => Some [$ v2 : term, c $]

      | _ => None
      end.
  Definition next_conf (_ : entropy) := dnext_conf.

  Definition transition st1 st2 := dnext_conf st1 = Some st2.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Fact trans_dcomputable :                              forall (st1 st2 : configuration),
       `(rws) st1 → st2 <-> dnext_conf st1 = Some st2.

  Proof. intuition. Qed.


  Fact trans_computable :                                                 forall st1 st2,
       `(rws) st1 → st2 <-> exists e, next_conf e st1 = Some st2.

  Proof. 
    intuition. 
    - destruct (draw_fin_correct 1 Fin.F1) as [e _]; exists e; auto.
    - destruct H; eauto.
  Qed.


  Theorem dnext_conf_eq_EAM :                                                  forall st,
      dnext_conf st = MiniML_EAM.dnext_conf st.

  Proof.
    destruct st as [t k ? | k c v].
    - destruct t, k; compute; auto.
    - destruct c as [| [] [] ec c]; auto.
      destruct ec; destruct v; 
      try solve
      [ compute; auto
      | match goal with v : value' |- _ => 
        destruct v; compute; auto 
        end ].
  Qed.


  Corollary next_conf_eq_EAM :                                               forall e st,
      next_conf e st = MiniML_EAM.next_conf e st.

  Proof. eauto using dnext_conf_eq_EAM. Qed.


  Corollary transition_eqv_EAM :                                          forall st1 st2,
      `(MiniML_EAM.rws) st1 → st2  <->  `(rws) st1 → st2.

  Proof.
    intros.
    rewrite trans_computable, MiniML_EAM.trans_computable.
    unfold MiniML_EAM.next_conf, next_conf.
    rewrite dnext_conf_eq_EAM.
    intuition.
  Qed.


  Proposition final_correct :                                                  forall st,
       final st <> None -> ~exists st', `(rws) st → st'.

  Proof.
    destruct st as [? | ? c v]; auto.
    destruct c; auto.
    intros _ [st' H].
    inversion H.
  Qed.


  Class SafeRegion (P : configuration -> Prop) :=
  {
      preservation :                                                      forall st1 st2,
          P st1  ->  st1 → st2  ->  P st2;
      progress :                                                              forall st1,
          P st1  ->  is_final st1 \/ (exists st2, st1 → st2)
  }.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition load          := load.
  Definition final         := final.
  Definition is_final c := exists v, final c = Some v.

End MiniML_HandMachine.
