Require Import Program
               Entropy
               Util
               rewriting_system
               lam_no
               abstract_machine
               reduction_semantics
               reduction_languages_facts.




Module Lam_NO_HandDecProc.

  Module RF := RED_LANG_Facts Lam_NO_PreRefSem.
  Import Lam_NO_PreRefSem RF.



  Inductive dec_proc {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_Var    : forall x {k2} (c : context k1 k2) d,
                 decctx_proc (vVar x) c d ->
                 dec_proc (Var x) c d

  | d_LamE   : forall x t (c : context k1 Eᵏ) d,
                 dec_proc t (k_lam_c x =: c) d ->   (*!*)
                 dec_proc (Lam x t) c d
  | d_LamF   : forall x t (c : context k1 Fᵏ) d,
                 decctx_proc (vFLam x t) c d -> (*!*)
                 dec_proc (Lam x t) c d

  | d_App    : forall t1 t2 {k2} (c : context k1 k2) d,
                 dec_proc t1 (k_ap_r t2 =: c) d ->
                 dec_proc (App t1 t2) c d


  with decctx_proc {k1} : forall {k2}, value k2 -> 
                              context k1 k2 -> decomp k1 -> Prop :=

  | dc_end        : forall (v : value k1),
                      decctx_proc v [.] (d_val v)

  | dc_ap_rLam    : forall x t0 t {k2} (c : context k1 k2),
                      decctx_proc (vFLam x t0) (k_ap_r t =: c) (d_red (rApp x t0 t) c)

  | dc_ap_rVar    : forall x t {k2} (c : context k1 k2) d,
                      dec_proc t (k_ap_l (vAVar x) =: c) d ->
                      decctx_proc (vVar x) (k_ap_r t =: c) d

  | dc_ap_rApp    : forall v1 v2 t {k2} (c : context k1 k2) d,
                      dec_proc t (k_ap_l (vAApp v1 v2) =: c) d ->
                      decctx_proc (vApp v1 v2) (k_ap_r t =: c) d

  | dc_ap_l       : forall v1 v2 {k2} (c : context k1 k2) d,
                      decctx_proc (vApp v1 v2) c d ->
                      decctx_proc v2 (k_ap_l v1 =: c) d

  | dc_lam_cE     : forall v x (c : context k1 Eᵏ) d,
                      decctx_proc (vELam x v) c d ->
                      decctx_proc v (k_lam_c x =: c) d.

  Scheme dec_proc_Ind    := Induction for dec_proc    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc Sort Prop.


  Module RS := Lam_NO_RefSem.


  Hint Constructors RS.refocus_in RS.refocus_out dec_proc decctx_proc.
  Hint Transparent Lam_NO_Strategy.dec_term Lam_NO_Strategy.dec_context.

  Theorem dec_proc_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      dec_proc t c d <-> RS.refocus_in t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) {
    induction H using dec_proc_Ind with
    (P0 := fun _ v c d _ => RS.refocus_out v c d);

    try solve
    [ eauto 
    | destruct k2; eauto];

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
    | H : RS.dec_term ?t ?k = _     |- _ => destruct t, k2;
                                            dependent destruction H; subst
    | H : RS.dec_context ?ec ?v = _ |- _ => destruct ec;
                                            dependent_destruction2 v;
                                            dependent destruction H; subst
    end; eauto.
 }
 Qed.


  Theorem decctx_proc_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d <-> RS.refocus_out v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    induction H using decctx_proc_Ind with
    (P := fun _ t c d _ => RS.refocus_in t c d); 

    try solve
    [ eauto
    | destruct k2; eauto ];

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
    | H : RS.dec_term ?t ?k = _     |- _ => destruct t, k2;
                                            dependent destruction H; subst
    | H : RS.dec_context ?ec ?v = _ |- _ => destruct ec;
                                            dependent_destruction2 v;
                                            dependent destruction H; subst
    end; 
    solve [eauto].
  }
  Qed.

End Lam_NO_HandDecProc.




Module Lam_NO_HandMachine <: ABSTRACT_MACHINE.

  Module R  := Lam_NO_PreRefSem.
  Module RF := RED_LANG_Facts R.


  Definition term := R.term.
  Inductive ckind := Eᵏ | Fᵏ.


  Definition ckind_to_R k : R.ckind :=
      match k with Eᵏ => R.Eᵏ | Fᵏ => R.Fᵏ end.

  Definition ckind_from_R k : ckind :=
      match k with R.Eᵏ => Eᵏ | R.Fᵏ => Fᵏ end.


  Definition val k := R.value (ckind_to_R k).
  Definition value := val Eᵏ.


  Inductive context : ckind -> Set :=
  | ap_r  : R.term  -> forall k, context k  -> context Fᵏ
  | ap_l  : R.valA  -> forall k, context k  -> context Eᵏ
  | lam_c : R.var   ->           context Eᵏ -> context Eᵏ
  | hole  : context Eᵏ.


  Inductive conf :=
  | Ev : R.term -> forall k, context k   -> conf
  | Ap : forall k (c : context k), val k -> conf.
  Definition configuration := conf.


  Definition load (t : term) : configuration := Ev t Eᵏ hole.


  Definition final (st : configuration) : option value :=
      match st with
      | Ap E hole v => Some v
      | _           => None
      end.


  Definition is_final (st : configuration) := exists v, final st = Some v.


  Definition dnext_conf (st : configuration) : option configuration :=
      match st with
      | Ev (R.Var x) k c       => Some (Ap k c (R.vVar x))

      | Ev (R.Lam x t) Eᵏ c    => Some (Ev t _ (lam_c x c))   (*!*)
      | Ev (R.Lam x t) Fᵏ c    => Some (Ap _ c (R.vFLam x t)) (*!*)

      | Ev (R.App t1 t2) k c   => Some (Ev t1 Fᵏ (ap_r t2 k c))

      | Ap Fᵏ (ap_r t2 k c) (R.vFLam x t1) =>
                                 Some (Ev (R.subst x t2 t1) k c)

      | Ap _ (ap_r t k c)   (R.vApp a v)   =>
                                 Some (Ev t Eᵏ (ap_l (R.vAApp a v) k c))

      | Ap _ (ap_r t k c)   (R.vVar x)     =>
                                 Some (Ev t Eᵏ (ap_l (R.vAVar x) k c))

      | Ap Eᵏ (ap_l a k c)  v  => Some (Ap k c (R.vApp a v))

      | Ap Eᵏ (lam_c x c)   v  => Some (Ap Eᵏ c (R.vELam x v))

      | _                      => None
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
    - destruct (entropy_exists) as [e _]; exists e; auto.
    - destruct H; eauto.
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
          P st1  ->  is_final st1 \/ exists st2, st1 → st2
  }.




  Program Fixpoint context_to_R {k} (c : context k) : R.context R.Eᵏ (ckind_to_R k) :=
      match c with
      | ap_r t k' c' => pcons (R.k_ap_r t)  (context_to_R c')
      | ap_l a k' c' => pcons (R.k_ap_l a)  (context_to_R c')
      | lam_c x c'   => pcons (R.k_lam_c x) (context_to_R c')
      | hole         => empty
      end.


  Program Fixpoint context_from_R
      {k} (c : R.context R.Eᵏ k) : context (ckind_from_R k) :=

      match c with
      | [.] => hole
      | ec=:c' =>
            match ec with
            | R.k_ap_r t  => ap_r t (ckind_from_R _) (context_from_R c')
            | R.k_ap_l a  => ap_l a (ckind_from_R _) (context_from_R c')
            | R.k_lam_c x => lam_c x (context_from_R c')
            end
      end.


  Lemma context_from_to_R_eq :                                forall {k} (c : context k),
      context_from_R (context_to_R c) ~= c.

  Proof.
    induction c as [t k c | v k c | x c | ];
    [ destruct c
    | destruct c
    | simpl
    | ].

    all: try solve [
         apply JM_eq_from_eq;
         simpl; f_equal;
         apply JMeq_eq; 
         apply IHc ].

    1:   solve [auto].
  Qed.


  Lemma context_to_from_R_eq :                         forall {k} (c : R.context R.Eᵏ k),
      context_to_R (context_from_R c) ~= c.

  Proof.
    induction c as [ | _ k [x | v | t ] c];
    [
    | destruct k
    | destruct k
    | ].

    1:   solve [auto].

    all: try solve [
      apply JM_eq_from_eq;
      simpl; f_equal;
      apply JMeq_eq; 
      apply IHc].

    all: try solve [autof].

    all:
      let tac := (
          apply JM_eq_from_eq;
          simpl; f_equal;
          apply JMeq_eq;
          apply IHc)
      in

      solve 
      [ dependent destruction c; auto; destruct k2, ec; inversion x0; dep_subst; tac
      | dependent destruction c; auto; destruct k2, ec; autof; tac].
  Qed.




  Module EAM := Lam_NO_EAM.

  Program Definition conf_to_R (st : configuration) : EAM.configuration :=
      match st with
      | Ev t _ c => EAM.c_eval t (context_to_R c)
      | Ap _ c v => EAM.c_apply  (context_to_R c) v
      end.


  Program Definition conf_from_R (st : EAM.configuration) : configuration :=
      match st with
      | @EAM.c_eval t k c  => Ev t (ckind_from_R k) (context_from_R c)
      | @EAM.c_apply k c v => Ap   (ckind_from_R k) (context_from_R c) v
      end.
  Next Obligation. destruct_all R.ckind; autof. Defined.


  Theorem conf_from_to_R_eq :                                forall (st : configuration),
      conf_from_R (conf_to_R st) = st.

  Proof.
    intro st.
    destruct st as [t k c | k c v].
    all: set (k0 := k);
         destruct k; try solve [inversion c].
    all: first [apply (f_equal (Ev t k0)) | apply (f_equal2 (Ap k0))].
    all: apply JMeq_eq;
         eauto using (context_from_to_R_eq c).
  Qed.


  Theorem conf_to_from_R_eq :                            forall (st : EAM.configuration),
      conf_to_R (conf_from_R st) = st.

  Proof.
    intro st.
    destruct st as [t k c | k c v].
    all: set (k0 := k);
         destruct k; try solve [inversion W].
    all: first [ apply (f_equal  (@EAM.c_eval t k0)) 
               | apply (f_equal2 (@EAM.c_apply k0))].
    all: apply JMeq_eq;
         eauto using (context_to_from_R_eq c).
  Qed.


  Theorem dnext_imp_EAM :                                                      forall st,
      option_map conf_to_R (dnext_conf st) = EAM.dnext_conf (conf_to_R st).

  Proof.
    intro st.
    destruct st as [t k c | k c v].
    - destruct t, c; simpl;
      solve [auto].
    - destruct c as [ ? ? c | ? ? c | ? ? | ]; compute in v; dependent destruction v;
      try destruct c;
      try solve [simpl; autof].
  Qed.


  Corollary next0_fol_EAM :                                                    forall st,
      option_map conf_from_R (EAM.dnext_conf st) = dnext_conf (conf_from_R st).

  Proof.
    intro st.
    rewrite <- (conf_to_from_R_eq st) at 1.
    rewrite <- (dnext_imp_EAM (conf_from_R st)).
    destruct (dnext_conf (conf_from_R st)); simpl.
    1  : rewrite conf_from_to_R_eq.
    all: solve [auto].
  Qed.

End Lam_NO_HandMachine.
