Set Printing Coercions.

Require Import Util
               Entropy
               Program
               rewriting_system
               refocusing_semantics
               abstract_machine
               refocusing_machine
               reduction_languages_facts
               lam_ses_no.



(* The module contains a hand-made refocusing (decomposition) procedure for the language
   defined in lam_ses_no.v and a proof that the automatically generated procedure is
   equivalent to it *)

Module Lam_SES_NO_HandDecProc.

  Module RF := RED_LANG_Facts Lam_SES_NO_PreRefSem.
  Import Lam_SES_NO_PreRefSem RF.


  (* The refocusing procedure in the form of inference rules.
     - refocus_in decomposes a term in a context
     - refocus_out backtracks from a value and looks for a redex in a context above *)

  Inductive refocus_in {k1} :  forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=
  | d_Var    : forall n {k2} (c : context k1 k2) d,
                 refocus_out (vVar n k2) c d ->
                 refocus_in (Var n) c d

  | d_LamE   : forall t (c : context k1 Eᵏ) d,
                 refocus_in t (lam_c =: c) d -> (*!*)
                 refocus_in (Lam t) c d
  | d_LamF   : forall t (c : context k1 Fᵏ) d,
                 refocus_out (vFLam t) c d ->   (*!*)
                 refocus_in (Lam t) c d
  | d_LamD   : forall t (c : context k1 Dᵏ) d,
                 refocus_out (vDLam t) c d ->   (*!*)
                 refocus_in (Lam t) c d

  | d_App    : forall t1 t2 {k2 : EF_kind} (c : context k1 k2) d,
                 refocus_in t1 (ap_r k2 t2 =: c) d ->
                 refocus_in (App t1 t2) c d

  | d_AppD   : forall t1 t2 (c : context k1 Dᵏ) d,
                 refocus_out (vDApp t1 t2) c d ->
                 refocus_in (App t1 t2) c d

  | d_Sub    : forall t1 n t2 {k2} (c : context k1 k2) d,
                 refocus_in t1 (esub_c _ (n, st_sub t2) =: c) d ->
                 refocus_in (Sub t1 n t2) c d

  | d_Shift  : forall t1 n m {k2} (c : context k1 k2) d,
                 refocus_in t1 (esub_c _ (n, st_shift m) =: c) d ->
                 refocus_in (Shift t1 n m) c d


  (* E.g., the constructor d_App stands for the rule

   refocus_in(t1, c[[]_F t2]) = d
  -------------------------------- for k = E,F
   refocus_in(t1 t2, c[[]_k]) = d


  and the constructor d_AppD for the rule

   refocus_out(t1 t2, c[[]_D])
  -----------------------------
   refocus_in(t1 t2, c[[]_D])

  *)

  with refocus_out {k1} : forall {k2}, value k2 ->
                              context k1 k2 -> decomp k1 -> Prop :=

  | dc_end         : forall (v : value k1),
                       refocus_out v [.] (d_val v)

  | dc_ap_rLamE    : forall t0 t (c : context k1 Eᵏ),
                       refocus_out (vFLam t0) (ap_r Eᵏ' t =: c) (d_red (rEApp t0 t) c)
  | dc_ap_rLamF    : forall t0 t (c : context k1 Fᵏ),
                       refocus_out (vFLam t0) (ap_r Fᵏ' t =: c) (d_red (rFApp t0 t) c)

  | dc_ap_rVarE    : forall n t (c : context k1 Eᵏ) d,
                       refocus_in t (ap_l Eᵏ' (vEaVar n) =: c) d ->
                       refocus_out (vFVar n) (ap_r Eᵏ' t =: c) d
  | dc_ap_rVarF    : forall n t (c : context k1 Fᵏ) d,
                       refocus_in t (ap_l Fᵏ' (vEaVar n) =: c) d ->
                       refocus_out (vFVar n) (ap_r Fᵏ' t =: c) d

  | dc_ap_rAppE    : forall v1 v2 t (c : context k1 Eᵏ) d,
                       refocus_in t (ap_l Eᵏ' (vEaApp v1 v2) =: c) d ->
                       refocus_out (vFApp v1 v2) (ap_r Eᵏ' t =: c) d
  | dc_ap_rAppF    : forall v1 v2 t (c : context k1 Fᵏ) d,
                       refocus_in t (ap_l Fᵏ' (vEaApp v1 v2) =: c) d ->
                       refocus_out (vFApp v1 v2) (ap_r Fᵏ' t =: c) d

  | dc_ap_lE       : forall v1 v2 (c : context k1 Eᵏ) d,
                       refocus_out (vEApp v1 v2) c d ->
                       refocus_out v2 (ap_l Eᵏ' v1 =: c) d
  | dc_ap_lF       : forall v1 v2 (c : context k1 Fᵏ) d,
                       refocus_out (vFApp v1 v2) c d ->
                       refocus_out v2 (ap_l Fᵏ' v1 =: c) d

  | dc_lam_cE      : forall v (c : context k1 Eᵏ) d,
                       refocus_out (vELam v) c d ->
                       refocus_out v (lam_c =: c) d

  | dc_sub_cLam   : forall t d {k2} (c : context k1 k2),
                       refocus_out (vDLam t) (esub_c _ d =: c)
                                   (d_red (rSubLam k2 t d) c)

  | dc_sub_cVar   : forall n d {k2} (c : context k1 k2),
                       refocus_out (vDVar n) (esub_c _ d =: c)
                                   (d_red (rSubVar k2 n d) c)

  | dc_sub_cApp   : forall t1 t2 d {k2} (c : context k1 k2),
                       refocus_out (vDApp t1 t2) (esub_c _ d =: c)
                                   (d_red (rSubApp k2 t1 t2 d) c).

  (* E.g., the constructor d_App stands for the rule

  ------------------------------------------------------
   refocus_out(\t0, c[[[]_F t]_E]) = ((\t0) t, c[[]_E])

  *)

  Scheme refocus_in_Ind  := Induction for refocus_in  Sort Prop
    with refocus_out_Ind := Induction for refocus_out Sort Prop.


  (* A dirty hack used to automatize unification *)
  Lemma d_App': forall k1 t1 t2  (c : context k1 Eᵏ) (c' : context k1 Eᵏ') d,
      c = c' -> refocus_in t1 (ap_r _ t2 =: c') d -> refocus_in (App t1 t2) c d.

  Proof.
    intros.
    apply (@d_App _ t1 t2 Eᵏ' ). rewrite H;auto.
  Qed.


  (* This module conatians a generated refocusing procedure *)
  Module RS := Lam_SES_NO_RefSem.

  Hint Constructors RS.refocus_in RS.refocus_out refocus_in refocus_out.
  Hint Transparent Lam_SES_NO_Strategy.dec_term Lam_SES_NO_Strategy.dec_context.


  Theorem refocus_in_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      refocus_in t c d <-> RS.refocus_in t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) {
    induction H using refocus_in_Ind with
    (P0 := fun _ v c d _ => RS.refocus_out v c d);
    solve
    [ try destruct k2; simpl in *; eautof
    | match goal with c : RS.context _ ?k |- RS.refocus_out _ (?ec =: c) _ => 
      solve
      [ eapply (RS.ro_red ec c); eauto
      | eapply (RS.ro_val ec c); eauto
      | eapply (RS.ro_step ec c); eauto ]
      end ].
  }

  (* <- *) {
    induction H using RS.refocus_in_Ind with
    (P0 := fun _ v c d _ => refocus_out v c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _     |- _ => destruct t, k;
                                                  dependent destruction H; subst;
                                                  try eapply (@d_App _ t0 t2 Eᵏ' c d);
                                                  try eapply (@d_App _ t0 t2 Fᵏ' c d)
    | H : RS.ST.dec_context ?ec ?v = _ |- _ => dependent destruction ec;
                                                  destruct_all EF_kind;
                                                  dependent_destruction2 v;
                                                  match goal with
                                                  | H : RS.ST.dec_context ?ec ?v = _ |- _
                                                    => dependent_destruction2 H; subst
                                                  end
    end;
    eauto.
  }
  Qed.


  Theorem refocus_out_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      refocus_out v c d <-> RS.refocus_out v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    induction H using refocus_out_Ind with
    (P := fun _ t c d _ => RS.refocus_in t c d);
    try solve
    [ try destruct k2; simpl in *; eautof
    | match goal with c : RS.context _ ?k |- RS.refocus_out _ (?ec =: c) _ =>
      solve
      [ eapply (RS.ro_red ec c);  eauto
      | eapply (RS.ro_val ec c);  eauto
      | eapply (RS.ro_step ec c); eauto ]
      end ].
  }

  (* <- *) {
    induction H using RS.refocus_out_Ind with
    (P := fun _ t c d _ => refocus_in t c d);

    try match goal with
    | H : RS.ST.dec_term ?t ?k = _     |- _ => destruct t, k; 
                                                  dependent_destruction2 H; subst;
                                                  try eapply (@d_App _ t0 t2 Eᵏ' c d);
                                                  try eapply (@d_App _ t0 t2 Fᵏ' c d)
    | H : RS.ST.dec_context ?ec ?v = _ |- _ => dependent_destruction2 ec;
                                                  destruct_all EF_kind;
                                                  dependent_destruction2 v;
                                                  dependent_destruction2 H; subst;
                                                  try match goal with
                                                  | H : RS.ST.dec_context ?ec ?v = _ |- _
                                                    => dependent_destruction2 H; subst
                                                  end
    end;
    eauto.
  }
  Qed.

End Lam_SES_NO_HandDecProc.




(* The module contains a hand-made abstract machine for the language
   defined in lam_ses_no.v and a proof that the automatically generated machine is
   equivalent to it *)

Module Lam_SES_NO_HandMachine <: ABSTRACT_MACHINE.

  Import Lam_SES_NO_EAM Lam_SES_NO_PreRefSem.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition load          := load.
  Definition final         := final.
  Definition is_final c    := exists v, final c = Some v.


  Notation "[$ t $]"       := ( (c_eval t [.]) : configuration)                      (t at level 99).
  Notation "[: v :]"       := ( (c_apply [.] v) 
                                   : configuration)                      (v at level 99).
  Notation "[$ t , k , c $]" := (@c_eval t k c )              (t, c at level 99).
  Notation "[: c , v  :]"     := (c_apply c v )                (c, v at level 99).
  Notation "[: ( ec , k ) =: c , v  :]" := 
      (c_apply (@ccons _ k _  ec c) v )                       (ec, k, c, v at level 99).

  Definition dnext_conf (st : configuration) : option configuration :=
      match st with

      | [$ Var n, k, c $]   => Some [: c, vVar n k :]

      | [$ Lam t, Dᵏ, c $] => Some [: c, vDLam t :]
      | [$ Lam t, Fᵏ, c $] => Some [: c, vFLam t :]
      | [$ Lam t, Eᵏ, c $] => Some [$ t, Eᵏ, lam_c =: c $]

      | [$ App t1 t2, Dᵏ, c $]  => Some [: c, vDApp t1 t2 :]
      | [$ App t1 t2, Fᵏ, c $]  => Some [$ t1, Fᵏ, (ap_r Fᵏ' t2) =: c  $]
      | [$ App t1 t2, Eᵏ, c $]  => Some [$ t1, Fᵏ, (ap_r Eᵏ' t2) =: c  $]

      | [$ Sub t1 j t2,  k, c $] => Some [$ t1, _, esub_c _ (j, st_sub t2) =: c $]
      | [$ Shift t1 j g, k, c $] => Some [$ t1, _, esub_c _ (j, st_shift g) =: c $]

       (* aux_D *)

       | [: esub_c _ d =: c, vDApp t1 t2 :] => 
                                      Some [$ contract0 (rSubApp Dᵏ t1 t2 d), _, c$]

       | [: esub_c _ d =: c, vDLam t :] => 
                                      Some [$ contract0 (rSubLam Dᵏ t d) , _ , c $]

       | [: esub_c _ d =: c, vDVar i :] => 
                                      Some [$ contract0 (rSubVar Dᵏ i d), _, c$]

       (* aux_C *)

       | [: (ap_r _ t2, Fᵏ) =: c, vFVar i :] => 
                                      Some [$ t2, Eᵏ, ap_l Fᵏ' (vEaVar i) =: c$]
       | [: (ap_r Eᵏ' t2, Eᵏ)   =: c, vFVar i :] => 
                                      Some [$ t2, Eᵏ, ap_l Eᵏ' (vEaVar i) =: c$]

       | [: (ap_r _ t2, Fᵏ) =: c, vFApp v1 v2 :] => 
                                      Some [$ t2, Eᵏ, ap_l Fᵏ' (vEaApp v1 v2) =: c$]
       | [: (ap_r _ t2, Eᵏ)   =: c, vFApp v1 v2 :] => 
                                      Some [$ t2, Eᵏ, ap_l Eᵏ' (vEaApp v1 v2) =: c$]

       | [: (ap_r Fᵏ' t2, Fᵏ) =: c, vFLam t1 :] => 
                                      Some [$ contract0 (rFApp t1 t2), Fᵏ, c$]
       | [: (ap_r Eᵏ' t2, Eᵏ)   =: c, vFLam t1 :] => 
                                      Some [$ contract0 (rFApp t1 t2), Eᵏ, c$]

       (* aux_A *)

       | [: (ap_l Fᵏ' v1, Fᵏ) =: c, v2 :] => Some [: c, vFApp v1 v2 :]
       | [: (ap_l Eᵏ' v1, Eᵏ) =: c, v2 :] => Some [: c, vEApp v1 v2 :]

       | [: (lam_c, Eᵏ)   =: c, v :]  => Some [: c, vELam v :]

       | _ => None
       end.

  Definition next_conf (_ : entropy) := dnext_conf.

  Definition transition st1 st2 := dnext_conf st1 = Some st2.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Fact trans_computable0 :                              forall (st1 st2 : configuration),
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
      dnext_conf st = Lam_SES_NO_EAM.dnext_conf st.

  Proof. intro st.
    destruct st.
    - destruct t, k; eauto.
    - dependent destruction c.
      eauto.
      dependent destruction ec; eauto; dependent destruction k;  dependent destruction v; eauto.
  Qed.


  Corollary next_conf_eq_EAM :                                               forall e st,
      next_conf e st = Lam_SES_NO_EAM.next_conf e st.

  Proof. eauto using dnext_conf_eq_EAM. Qed.


  Corollary transition_eqv_EAM :                                          forall st1 st2,
      `(Lam_SES_NO_EAM.rws) st1 → st2  <->  `(rws) st1 → st2.

  Proof.
    intros.
    rewrite trans_computable, Lam_SES_NO_EAM.trans_computable.
    unfold Lam_SES_NO_EAM.next_conf, next_conf.
    rewrite dnext_conf_eq_EAM.
    intuition.
  Qed.


  Proposition final_correct :                                                  forall st,
       final st <> None -> ~exists st', `(rws) st → st'.

  Proof.
    destruct st ; auto.
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

End Lam_SES_NO_HandMachine.
