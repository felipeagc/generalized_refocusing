Require Import Util
               Program
               refocusing_semantics.



Module MiniML_PreRefSem <: PRE_REF_SEM.

  Parameter var : Set.


  Inductive expr :=
  | Z   : expr
  | S   : expr -> expr
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr
  | Case: expr -> expr -> var -> expr -> expr
  | Letv: var -> expr -> expr -> expr
  | Fix : var -> expr -> expr
  | Pair: expr -> expr -> expr
  | Fst : expr -> expr
  | Snd : expr -> expr.
  Definition term := expr.
  Hint Unfold term.


  Definition ckind := unit.
  Hint Unfold ckind.


  Inductive val :=
  | vZ    : val
  | vS    : val -> val
  | vLam  : var -> term -> val
  | vVar  : var -> val
  | vPair : val -> val -> val.
  Definition value (_ : ckind) := val.
  Hint Unfold value.
  Notation value' := (value ()).

  Coercion val_value := id : val -> value'.


  Inductive red :=
  | rApp : value' -> value' -> red
  | rLet : var -> value' -> term -> red
  | rFix : var -> term -> red
  | rFst : value' -> red
  | rSnd : value' -> red
  | rCase: value' -> term -> var -> term -> red.
  Definition redex (_ : ckind) := red.
  Hint Unfold redex.
  Notation redex' := (redex ()).

  Coercion red_redex := id : red -> redex'.


  Inductive ec :=
  | s_c    : ec
  | ap_l   : value' -> ec
  | ap_r   : term -> ec
  | case_c : term -> var -> term -> ec
  | let_c  : var -> term -> ec
  | fst_c  : ec
  | snd_c  : ec
  | pair_l : value' -> ec
  | pair_r : term -> ec.
  Definition elem_context_kinded (_ _ : ckind) : Type := ec.


  Definition init_ckind : ckind := ().
  Hint Unfold init_ckind.

  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vZ          => Z
      | vS v        => S (@value_to_term () v)
      | vLam x t    => Lam x t
      | vVar x      => Var x
      | vPair v1 v2 => Pair (@value_to_term () v1) (@value_to_term () v2)
      end.
  Coercion value_to_term : value >-> term.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp v1 v2      => App (v1 : term) (v2 : term)
      | rLet x v t      => Letv x (v : term) t
      | rFix x v        => Fix x (v : term)
      | rFst v          => Fst (v : term)
      | rSnd v          => Snd (v : term)
      | rCase v t1 x t2 => Case (v : term) t1 x t2
      end.
  Coercion redex_to_term : redex >-> term.


  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof.
    destruct k.

    induction v;
        destruct v';
        inversion 1;

    solve [ f_equal; auto ].
  Qed.


  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    destruct k.

    destruct r; destruct r';
    inversion 1;

    solve [ f_equal; auto using value_to_term_injective ].
  Qed.


  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | s_c            => S t
      | ap_l v         => App (v : term) t
      | ap_r t2        => App t t2
      | case_c t1 x t2 => Case t t1 x t2
      | let_c x t2     => Letv x t t2
      | fst_c          => Fst t
      | snd_c          => Snd t
      | pair_l v       => Pair (v : term) t
      | pair_r t2      => Pair t t2
      end.


  Parameter subst : var -> term -> term -> term.

  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp (vLam x t) v  => Some (subst x v t)
      | rLet x v t         => Some (subst x v t)
      | rFix x e           => Some (subst x (Fix x e) e)
      | rFst (vPair v1 v2) => Some ((v1 : value') : term)
      | rSnd (vPair v1 v2) => Some ((v2 : value') : term)
      | rCase vZ t _ _     => Some t
      | rCase (vS v) _ x t => Some (subst x (v : value') t)
      | _                  => None
      end.
  Notation contract' := (@contract ()).

  Include RED_SEM_BASE_Notions.

  Notation context' := (context () ()).
  Notation decomp'  := (@decomp ()).


  Lemma elem_plug_injective1 :     forall {k1 k2} (ec : elem_context_kinded k1 k2) t0 t1,
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec ? ? H.

    destruct ec;
    inversion H;
    solve [ trivial ].
  Qed.



  Lemma value_trivial1 :
  forall {k1 k2} (ec:elem_context_kinded k1 k2) t,
       forall v : value k1,  ec:[t] = v ->
           exists (v' : value k2), t = v'.

  Proof.
    intros [] [] ec t v H.
    destruct ec, v; inversion H; subst;
    eauto.
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof.
    destruct v; destruct r; intro H; discriminate H.
  Qed.


  Lemma redex_trivial1 : forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
                             ec:[t] = r ->
                                 exists (v : value k'), t = v.
  Proof with auto.
    intros [] [] r ec t H.
    destruct ec, r; inversion H; subst;
    eauto.
  Qed.


  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.

  Definition wf_subterm_order : well_founded subterm_order
      := wf_clos_trans_l _ _ wf_immediate_subterm.

End MiniML_PreRefSem.




Module MiniML_Strategy <: REF_STRATEGY MiniML_PreRefSem.

  Import MiniML_PreRefSem.
  Include RED_STRATEGY_STEP_Notions MiniML_PreRefSem.

  Definition dec_term (t : term) k : elem_dec k :=
      match t with
      | Z              =>  ed_val vZ
      | S t            =>  ed_dec () t s_c
      | App t1 t2      =>  ed_dec () t1 (ap_r t2)
      | Var x          =>  ed_val (vVar x)
      | Lam x t        =>  ed_val (vLam x t)
      | Case t ez x es =>  ed_dec () t (case_c ez x es)
      | Letv x t e     =>  ed_dec () t (let_c x e)
      | Fix x t        =>  ed_red (rFix x t)
      | Pair t1 t2     =>  ed_dec () t1 (pair_r t2)
      | Fst t          =>  ed_dec () t fst_c
      | Snd t          =>  ed_dec () t snd_c
      end.


  Program Definition dec_context
          {k k'} (ec : elem_context_kinded k k') (v : value k') : elem_dec k :=

      match ec with
      | s_c             =>  ed_val (vS v)
      | ap_l v0         =>  ed_red (rApp v0 v)
      | ap_r t          =>  ed_dec () t (ap_l v)
      | case_c ez x es  =>  ed_red (rCase v ez x es)
      | let_c x e       =>  ed_red (rLet x v e)
      | fst_c           =>  ed_red (rFst v)
      | snd_c           =>  ed_red (rSnd v)
      | pair_l v0       =>  ed_val (vPair v0 v)
      | pair_r t        =>  ed_dec () t (pair_l v)
      end.


  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).

  Proof with auto.
    destruct k, t; simpl...
  Qed.


  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).

  Proof.
    intros k ec v.
    destruct k, ec; dependent destruction v;
    simpl;
    solve [ auto ].
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
      | ap_l _,   ap_r _   => immediate_ec ec t /\ immediate_ec ec0 t
      | pair_l _, pair_r _ => immediate_ec ec t /\ immediate_ec ec0 t
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



  Ltac inj_vr := match goal with
  | [Hv : value_to_term _ = value_to_term _ |- _] => apply value_to_term_injective in Hv
  | [Hr : redex_to_term _ = redex_to_term _ |- _] => apply redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.


  Lemma search_order_comp_if :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ( k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t [] [] [] ec0 ec1 H H0.

    assert (G := H); assert (G0 := H0).
    destruct H as (t0, H), H0 as (t1, H0).
    rewrite <- H in H0.

    destruct ec0, ec1; inversion H0;

    solve
    [ auto
    | inj_vr; subst;
      simpl;
      intuition constructor ].
  Qed.


  Lemma search_order_comp_fi :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

       k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t.

  Proof.
    intros t [] [] [] ec0 ec1 H.

    destruct ec0, ec1; inversion H;
    solve [ intuition ].
  Qed.


  Lemma dec_term_term_top :                                             forall k k' t t',

       forall (ec : elem_context_kinded k k'),
           dec_term t k = ed_dec _ t' ec -> so_maximal ec t.

  Proof.
    intros [] [] t t' ec H ec' H0.
    destruct t, ec;
        inversion H; subst;
        destruct ec';
    solve [ inversion H0 ].
  Qed.


  Lemma dec_context_red_bot :                                forall k k' v {r : redex k},

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].

  Proof.
    intros [] [] v r ec H [[] ec'] H0.
    destruct ec; dependent destruction ec';
    try solve [ inversion H; inversion H0 ].
  Qed.


  Lemma dec_context_val_bot :                               forall k k' v {v' : value k},

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_val v' -> so_minimal ec ec:[v].

  Proof.
    intros [] [] v v' ec H [[] ec'] H0.
    destruct ec, ec';
    solve [ inversion H; inversion H0 ].
  Qed.


  Lemma dec_context_term_next :                                      forall k0 k1 k2 v t,

      forall (ec0 : elem_context_kinded k0 k1) (ec1 : elem_context_kinded k0 k2),
          dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros [] [] [] v t ec0 ec1 H.

    assert (H0 := dec_context_correct ec0 v); rewrite H in H0.

    destruct ec0, ec1;
        inversion H; subst;

    solve [
        split;
        [ constructor;
          eexists; eauto
        | intros [[] ec''] H1 H2;
          destruct ec'';
          inversion H1; inversion H2
    ]   ].
  Qed.


  Lemma elem_context_det :            forall k0 k1 k2 t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

          t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].

  Proof.
    intros [] [] [] t ec ec' H.

    destruct ec, ec';
        inversion H; subst;

    solve
    [ inversion H0 as (t1, H0a);
      inversion H1 as (t2, H1a);
      assert (t0 = t1);
      try solve [simpl in *; congruence];
      subst;
      exists v; trivial ].
  Qed.

End MiniML_Strategy.



Module MiniML_RefSem := RedRefSem MiniML_PreRefSem MiniML_Strategy.




Require Import refocusing_machine.

Module MiniML_EAM := RefEvalApplyMachine MiniML_RefSem.
