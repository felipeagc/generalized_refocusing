(* Lambda calculus with left-to-right open call-by-value reduction strategy *)

Require Import Program
               Util
               String
               refocusing_semantics.

Open Scope string_scope.

Module Lam_open_cbv_PreRefSem <: PRE_RED_SEM.

  Definition var := string.

  Definition eq_var : forall x y : var, {x = y} + {x <> y} := string_dec.

  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr.
  Definition term := expr.
  Hint Unfold term.

  Inductive ck := Cᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.

  Inductive val : ckind -> Type :=
  | vLam : var -> term -> val Cᵏ
  | vInert : inert Cᵏ -> val Cᵏ
  with inert : ckind -> Type :=
  | vVar : var -> inert Cᵏ
  | vApp : inert Cᵏ -> val Cᵏ -> inert Cᵏ.

  Scheme val_Ind   := Induction for val Sort Prop
    with inert_Ind := Induction for inert Sort Prop.
  Combined Scheme all_values_ind from val_Ind, inert_Ind.

  Definition value := val.
  Hint Unfold value.

  Fixpoint value_to_term {k} (v : value k) : term :=
    match v with
    | vLam x t => Lam x t
    | vInert i => inert_to_term i
    end
  with inert_to_term {k} (i : inert k) : term :=
    match i with
    | vVar x    => Var x
    | vApp i' v => App (inert_to_term i') (value_to_term v)
    end.

  Coercion value_to_term : value >-> term.

  Inductive red : ckind -> Type :=
  | rApp : var -> term -> value Cᵏ -> red Cᵏ.
  Definition redex := red.
  Hint Unfold redex.

  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp x t v   => App (Lam x t) (value_to_term v)
      end.

  Lemma inert_to_term_not_Lam : forall k i x t, @inert_to_term k i <> Lam x t.
  Proof. induction i; intros x t H; inversion H. Qed.

  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof.
    eapply (proj1 (all_values_ind
      (fun c => fun v => forall v', value_to_term v = value_to_term v' -> v = v')
      (fun c => fun i => forall i', inert_to_term i = inert_to_term i' -> i = i')
      _ _ _ _)).
    Unshelve.
    + simpl. intros. dependent destruction v'.
      - inversion H. reflexivity.
      - symmetry in H. apply inert_to_term_not_Lam in H. contradiction.
    + simpl. intros. dependent destruction v'.
      - apply inert_to_term_not_Lam in H0. contradiction.
      - apply H in H0. f_equal. exact H0.
    + simpl. intros. dependent destruction i'; inversion H. reflexivity.
    + simpl. intros i IHi v IHv i' H.
      dependent destruction i'; inversion H.
      exact (f_equal2 vApp (IHi _ H1) (IHv _ H2)).
  Qed.

  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    intros k r r' H.
    dependent destruction r; dependent destruction r';
    inversion H; try apply (value_to_term_injective v0 v2)  in H3;  subst; reflexivity.
  Qed.

  Inductive eck : ckind -> ckind -> Type :=
  | ap_r  : term -> eck Cᵏ Cᵏ
  | ap_l  : value Cᵏ -> eck Cᵏ Cᵏ.

  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  Definition init_ckind : ckind     :=  Cᵏ.

  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      | ap_l  v  => App (v: term) t
      end.

  Reserved Notation "'[' x ':=' s ']' t" (at level 20).

  Fixpoint subst (x:var) (s:term) (t:term) : term :=
    match t with
    | Var x' =>
        if eq_var x x' then s else t
    | Lam x' t1 =>
        Lam x' (if eq_var x x' then t1 else ([x:=s] t1))
    | App t1 t2 =>
        App ([x:=s] t1) ([x:=s] t2)
    end
  where "'[' x ':=' s ']' t" := (subst x s t).

  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp x t0 t1 => Some ([x := t1] t0)
      end.

  Include RED_SEM_BASE_Notions.

  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    solve
    [ inversion H; trivial ].
  Qed.

  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof.    REF_LANG_Help.prove_st_wf.
  Qed.

  Definition wf_subterm_order : well_founded subterm_order
    := wf_clos_trans_l _ _ wf_immediate_subterm.

  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                             exists (v' : value k2), t = v'.
  Proof.
    intros ? ? ec t v H.
    destruct ec;
    dependent destruction v; inversion H;
    dependent destruction i; inversion H1.
    + exists (vInert i). reflexivity.
    + exists v. reflexivity.
  Qed.

  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r H.
    destruct r; destruct v; inversion H.
    dependent destruction i; inversion H.
    apply inert_to_term_not_Lam in H2. contradiction.
  Qed.

  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof.
    intros ? ? r ec t H.
    destruct r.
    destruct ec; inversion H.
    + exists (vLam v t0). reflexivity.
    + exists v0. reflexivity.
  Qed.

End Lam_open_cbv_PreRefSem.


Module Lam_open_cbv_Strategy <: REF_STRATEGY Lam_open_cbv_PreRefSem.

  Import Lam_open_cbv_PreRefSem.
  Include RED_STRATEGY_STEP_Notions Lam_open_cbv_PreRefSem.

  Definition dec_term t k : elem_dec k :=
    match k with Cᵏ =>
                 match t with
                 | App t1 t2 => ed_dec  Cᵏ t1 (ap_r t2)
                 | Var x     => ed_val (vInert (vVar x))
                 | Lam x t1  => ed_val (vLam x t1)
                 end
    end.

  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).
  Proof.
    destruct k,t ; simpl; auto.
  Qed.

  Definition dec_context  {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec in eck k k' return value k' -> elem_dec k with
    | ap_r t =>  (fun v => ed_dec Cᵏ t (ap_l v))
    | ap_l v' => (fun v => match v' with
                   | vLam x t => ed_red  (rApp x t v)
                   | vInert i => ed_val (vInert (vApp i v))
                   end)
    end v.

  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).

  Proof.
    intros ? ? ec v.
    destruct ec.
    * dependent destruction v; simpl; auto.
    * dependent destruction v0; simpl; auto.
  Qed.

  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop :=
    let (_, ec)  := ec  in
    let (_, ec0) := ec0 in
    match ec, ec0 with
    | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t
    | _, _           => False
    end.

  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).

  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
                                     (no associativity, at level 70, ec1, t at level 69).

  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof.
    intros k t [? ec];
    destruct t, ec;
    let k0 := fresh k  in
    repeat
    (let k0 := fresh k  in
     let ec := fresh ec in
     let H  := fresh H  in
     constructor;
     intros [k0 ec] H;
     dependent destruction ec;
     try discriminate;
     dep_subst;
     try (inversion H; dep_subst; clear H)).
  Qed.


  Lemma search_order_trans :  forall k t ec0 ec1 ec2,
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 ->
      k,t |~ ec0 << ec2.

  Proof.
    intros k t [? ec0] [? ec1] [? ec2] H H0.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    dep_subst;
    try solve [ autof ].
  Qed.

  Lemma search_order_comp_fi :
      forall t k k' k'' (ec0 : elem_context_kinded k k')
                        (ec1 : elem_context_kinded k k''),
          k, t |~ ec0 << ec1 ->
              immediate_ec ec0 t /\ immediate_ec ec1 t.


  Proof with auto.
    intros t k k'' k''' ec0 ec1 H.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    subst;
    inversion H;
    solve [auto].
  Qed.

  Lemma search_order_comp_if :   forall t k k' k'' (ec0 : elem_context_kinded k k')
      (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5);
    subst t;
    destruct ec0; dependent destruction ec1;
    try discriminate;
    subst;
    inversion H5; subst;

    try solve
    [ compute; eautof 7
    | do 2 right;
      split;
    [ auto
    | match goal with H : (value_to_term _) = (value_to_term _) |- _ =>
      apply value_to_term_injective in H;
      subst;
      auto
      end
    ] ].
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
  Proof.
    intros k k' t t' ec H ec' H0.
    destruct t, ec; dependent destruction ec'; destruct k';
    inversion H; inversion H0.
  Qed.

  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof.
    intros k k' ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    inversion H;
    dependent destruction v; dependent destruction e; dependent destruction r;
    intro G;  unfold search_order in G; simpl in G;
    solve
    [ autof
    | inversion H;
      intro G;
      unfold search_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0;
      autof ].

  Qed.

  Lemma dec_context_val_bot : forall {k k'} (v : value k') {v' : value k}
      (ec : elem_context_kinded k k'),
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
  Proof.
    intros ? ? v v' ec H [? ec'].
    destruct ec; dependent destruction ec'; dependent destruction v;
    try discriminate;
    subst;
    solve [ autof ].
  Qed.

  Lemma dec_context_term_next :                        forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].
  Proof.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0; dependent destruction ec1; dependent destruction v;
    try discriminate;
    subst;
    solve
    [ autof

    | inversion H; subst;
      split;
      [
        compute; eauto
      | intros [? ec''] H0 H1;
        dependent_destruction2 ec'';
        try discriminate;
        subst;
        solve [ autof ]
      ]
    |  unfold so_predecessor;
       split;
          compute; simpl in H;
       dependent_destruction2 v0;
       inversion H;
       intros [? ec''] H0 H1;
       dependent_destruction2 ec'';
       try discriminate;
       subst;
       solve [ autof ]
    ].
  Qed.

  Lemma elem_context_det :          forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].
  Proof.
    intros ? ? ? t ec0 ec1 H0.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    subst;
    autof.

   unfold search_order in H0; destruct H0 as (H, G).
   inversion G; inversion H; subst.
   inversion H1. dependent destruction v.
   + exists (vLam v t). reflexivity.
   + exists (vInert i). reflexivity.
 Qed.

End Lam_open_cbv_Strategy.

Module Lam_open_cbv_RefSem := RedRefSem Lam_open_cbv_PreRefSem Lam_open_cbv_Strategy.


Require Import refocusing_machine.

Module Lam_open_cbv_EAM := RefEvalApplyMachine Lam_open_cbv_RefSem.

Import Lam_open_cbv_PreRefSem.

Import Lam_open_cbv_EAM.


Require Import abstract_machine_facts.
Module Lam_open_cbv_sim := DetAbstractMachine_Sim Lam_open_cbv_EAM.
Import Lam_open_cbv_sim.

Definition ω := (Lam "x" (App (Var "x") (Var "x"))).
Definition I := (Lam "z" (Var "z")).
Definition t := (App ω I).

Eval compute in list_configurations t 15.

Print Lam_open_cbv_EAM.

