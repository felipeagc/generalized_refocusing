(*
Clean red sem for normal order should be sth like this:

E ::= F | \x.E | a E
F ::= []_F | F t

beta should be an F-redex
[] t : eck F F
a [] : eck E E

Maybe an explicit coercion from ec of kind F to E would help?

*)


(* Lambda calculus with normal order and substitutions in one step example *)


Require Import Program
               Util
               refocusing_semantics.



Module Lam_NO_PreRefSem <: PRE_REF_SEM.

  Parameter var : Set.


  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var  -> expr
  | Lam : var  -> expr -> expr.
  Definition term := expr.
  Hint Unfold term.

  Inductive  ck    := Eᵏ | Fᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.


  Inductive val : ckind -> Type :=

  | vELam : var -> val Eᵏ -> val Eᵏ
  | vVar : forall {k}, var -> val k
  | vApp : forall {k}, valA -> val Eᵏ -> val k
  | vFLam : var -> term -> val Fᵏ

  with valA :=

  | vAVar : var  -> valA
  | vAApp : valA -> val Eᵏ -> valA.

  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val  Sort Prop
    with valCa_Ind := Induction for valA Sort Prop.


  Inductive red : ckind -> Type :=
  | rApp : forall {k}, var -> term -> term -> red k.
  Definition redex := red.
  Hint Unfold redex.

  Inductive eck : ckind -> ckind -> Set :=
  | k_lam_c : var -> eck Eᵏ Eᵏ
  | k_ap_r  : forall {k}, term -> eck k Fᵏ
  | k_ap_l  : forall {k}, valA -> eck k Eᵏ .
  Definition elem_context_kinded : ckind -> ckind -> Type := eck.

  (*Inductive ec :=
  | lam_c : var -> ec
  | ap_r  : term -> ec
  | ap_l  : valA -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.*)

  (*Definition erase_kinds {k1 k2} (e : elem_context_kinded k1 k2) : elem_context :=
      match e with
      | k_lam_c x => lam_c x
      | k_ap_r t  => ap_r t
      | k_ap_l a  => ap_l a
      end.
  Coercion erase_kinds : elem_context_kinded >-> elem_context.*)


  Definition init_ckind : ckind :=  Eᵏ.

  Hint Unfold init_ckind.


  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vELam x v  => Lam x (value_to_term v)
      | vVar x     => Var x
      | vApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      | vFLam x t  => Lam x t
      end

  with valA_to_term v : term :=
      match v with
      | vAVar x     => Var x
      | vAApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valA_to_term  : valA >-> term.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp x t1 t2  => App (Lam x t1) t2
      end.
  Coercion redex_to_term : redex >-> term.

  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma valA_to_term_injective :
      forall v v', valA_to_term v = valA_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;

    solve
    [ destruct r;
      dependent destruction r';
      inversion H;
      f_equal; auto ].
  Qed.


  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | k_lam_c x => Lam x t
      | k_ap_r tr => App t tr
      | k_ap_l v  => App (v : term) t
      end.


  Parameter subst : var -> term -> term -> term.


  Definition contract0 {k} (r : redex k) : term :=
      match r with
      | rApp x t0 t1 => subst x t1 t0
      end.
  Definition contract {k} (r : redex k) := Some (contract0 r).

  Include RED_SEM_BASE_Notions.


  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros k1 k2 ec t0 t1 H.
    destruct ec;
    solve [ injection H; trivial ].
  Qed.


  Lemma valA_is_valF :
      forall v1 : valA, exists v2 : value Fᵏ, valA_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vVar v)...
    - exists (vApp v1 v)...
  Qed.


  Lemma value_trivial1 :
      forall {k1 k2} (ec:elem_context_kinded k1 k2) t,
          forall v : value k1,  ec:[t] = v ->
              exists (v' : value k2), t = v'.

  Proof.
    intros k1 k2 ec t v H.
    dependent destruction ec.
    dependent destruction v0;
    inversion H; subst; eautof.
    dependent destruction v;
    inversion H; subst; auto using valA_is_valF.
    dependent destruction v0;
    inversion H; subst;
    eauto.
  Qed.


  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof with auto.
    intros k k' r ec t H0.
    generalize dependent r.
    dependent destruction ec; intros; dependent destruction r; inversion H0; subst;
    solve
    [ eexists (vFLam _ _); reflexivity
    | eauto using valA_is_valF
    | destruct v; inversion H1 ].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v;
    simpl;
    try match goal with
    | |- App (valA_to_term ?v) _ <> _ => dependent_destruction2 v
    end;

    solve [ discriminate ].
  Qed.


  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.

  Definition wf_subterm_order : well_founded subterm_order
      := wf_clos_trans_l _ _ wf_immediate_subterm.

End Lam_NO_PreRefSem.




Module Lam_NO_Strategy <: REF_STRATEGY Lam_NO_PreRefSem.

  Import Lam_NO_PreRefSem.
  Include RED_STRATEGY_STEP_Notions Lam_NO_PreRefSem.


  Definition dec_term (t : term) (k : ckind) : elem_dec k :=

      match k as k0 return elem_dec k0 with
      | Eᵏ   => match t with
                | App t1 t2 => ed_dec _ t1 (k_ap_r t2)
                | Var x     => ed_val (vVar x)
                | Lam x t1  => ed_dec _ t1 (k_lam_c x)
                  end
      | Fᵏ   => match t with
                | App t1 t2 => ed_dec _ t1 (k_ap_r t2)
                | Var x     => ed_val (vVar x)
                | Lam x t1  => ed_val (vFLam x t1)
                end
       end.


  Program Definition dec_context
          {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k :=

      match ec in eck k k' return val k' -> elem_dec k with

      | k_lam_c x   => fun v => ed_val (vELam x v)

      | @k_ap_r k t => fun v =>
                          match v in val k' return k' = Fᵏ -> elem_dec k with
                          | vELam x v0 => _
                          | vVar x     => fun _ => ed_dec _ t (k_ap_l (vAVar x))
                          | vApp v1 v2 => fun _ => ed_dec _ t (k_ap_l (vAApp v1 v2))
                          | vFLam x t0 => fun _ => ed_red (@rApp k  x t0 t)
                          end refl_equal
      | k_ap_l v0  => fun v : val Eᵏ => ed_val (vApp v0 v)

     end v.


  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).

  Proof.
    destruct k, t; simpl;
    auto.
  Qed.


  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).

  Proof with auto.
    intros k k' ec.
    dependent destruction ec; simpl...
    intro; dependent destruction v;
    simpl...
  Qed.


  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.

  Definition search_order
      (k : ckind) t (ec ec0 : elem_context_in k) : Prop :=

      let (_, ec)  := ec  in
      let (_, ec0) := ec0 in

      match ec, ec0 with
      | k_ap_l _, k_ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t
      | _, _               => False
      end.

  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
                                (at level 70, t, ec1, ec2 at level 50, no associativity).

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


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_trans :                                      forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1  ->  k, t |~ ec1 << ec2  ->  k, t |~ ec0 << ec2.

  Proof.
    intros k t [k0 ec0] [k1 ec1] [k2 ec2] H H0.
    destruct ec0; dependent destruction ec1;
    solve [ autof ].
  Qed.


  Lemma search_order_comp_if :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ( k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.

    dependent destruction ec0; dependent destruction ec1;
    inversion H5; subst;

    solve
    [ compute; eautof 7
    | do 2 right;
      f_equal;
      apply valA_to_term_injective; auto
    | do 2 right;
      elim (valA_to_term_injective _ _ H0);
      auto ].
  Qed.


  Lemma search_order_comp_fi :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

       k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t.

  Proof with auto.
    intros t k k' k'' ec0 ec1 H.
    dependent destruction ec0; dependent destruction ec1;
    inversion H;
    solve [auto].
  Qed.


  Lemma dec_term_term_top :                                             forall k k' t t',

       forall (ec : elem_context_kinded k k'),
           dec_term t k = ed_dec _ t' ec -> so_maximal ec t.

  Proof.
    intros k k' t t' ec H ec' H0.
    destruct k, t, ec';
    revert H0;
    inversion H; subst; intro H0; inversion H0...
  Qed.


  Lemma dec_context_red_bot :                   forall k k' (v : value k') (r : redex k),

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].

  Proof.
    intros k k' v r ec H ec'.
    destruct ec; dependent destruction ec'; dependent destruction v;
    try solve
    [ autof
    | inversion H;
      intro G;
      unfold search_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0;
      autof ].

    (* TO REFACTOR *)
      intro H0;
      destruct e;
      inversion H0;
      destruct H1 as [t1 H1];
      inversion H1;
      destruct v0;
      inversion H4.
  Qed.


  Lemma dec_context_val_bot :                               forall k k' v {v' : value k},

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_val v' -> so_minimal ec ec:[v].

  Proof.
    intros k k' v v' ec H [k'' ec'].
    destruct ec; dependent destruction ec'; dependent destruction v;
    solve [ autof ].
  Qed.


  Lemma dec_context_term_next :                                      forall k0 k1 k2 v t,

      forall (ec0 : elem_context_kinded k0 k1) (ec1 : elem_context_kinded k0 k2),
          dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros k0 k1 k2 v t ec0 ec1 H.
    dependent destruction ec0;
    dependent destruction ec1;
    try dependent destruction v;
    solve
    [ autof

    | inversion H; subst;
      split;
      [ constructor;
        compute; eauto
      | intros [k'' ec''] H0 H1;
        destruct ec'';
        solve [ autof ]
      ] ].
  Qed.


  Lemma elem_context_det :            forall k0 k1 k2 t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

          t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].

  Proof.
    intros k0 k1 k2 t ec0 ec1 H.
    destruct ec0; dependent destruction ec1;
    autof.
    unfold search_order in H; destruct H as (H, G);
    destruct (valA_is_valF v) as (v0, H0).

    exists v0.
    simpl; rewrite <- H0.
    inversion H as (t1, H1).
    subst.
    inversion G as [t2 G2].
    inversion G2.
    trivial.
  Qed.

End Lam_NO_Strategy.



Module Lam_NO_RefSem := RedRefSem Lam_NO_PreRefSem Lam_NO_Strategy.



Require Import refocusing_machine.

Module Lam_NO_EAM := RefEvalApplyMachine Lam_NO_RefSem.
