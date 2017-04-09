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
  Definition elem_context_kinded (_ _ : ckind) : Set := ec.


  (*Definition erase_kinds {k1 k2} (e : elem_context_kinded k1 k2) : elem_context := e.
  Coercion erase_kinds : elem_context_kinded >-> elem_context.*)


(*  Definition ckind_trans (_ : ckind) (_ : elem_context) : ckind := ().
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).*)


  Definition init_ckind : ckind := ().
(*  Definition dead_ckind (_ : ckind) := False.*)
  Hint Unfold init_ckind (*dead_ckind*).


(*  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _. *)

  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons :                                                                forall {k2 k3}
            (ec : elem_context_kinded k2 k3), context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1 k2 k3} _ _.
  Notation context' := (context () ()).

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).


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


(*  Instance dead_is_comp : CompPred ckind dead_ckind.
      split. auto. 
  Defined.*)


(*  Lemma init_ckind_alive :
      ~dead_ckind init_ckind.

  Proof. auto. Qed. *)


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



(*  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end. *)

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


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
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Lemma elem_plug_injective1 :     forall {k1 k2} (ec : elem_context_kinded k1 k2) t0 t1,
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec ? ? H.

    destruct ec;
    inversion H;
    solve [ trivial ].
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec {k1 k2} (ec : elem_context_kinded k1 k2) t := 
      exists t', ec:[t'] = t.


(*  Lemma death_propagation : 
      forall k ec, dead_ckind k -> dead_ckind (k+>ec).

  Proof. auto. Qed.*)


(*  Lemma proper_death : forall k, dead_ckind k -> ~ exists (r : redex k), True.
  Proof. auto. Qed. *)


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


(*  Lemma value_trivial1 : forall {k} ec t, 
      forall (v : value k), ~dead_ckind (k+>ec) -> ec:[t] = v ->
          exists (v' : value (k+>ec)), t = v'. *)

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


(*  Lemma redex_trivial1 : forall {k} (r : redex k) ec t,
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.*)

  Lemma redex_trivial1 : forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
                             ec:[t] = r -> 
                                 exists (v : value k'), t = v.
  Proof with auto.
    intros [] [] r ec t H.
    destruct ec, r; inversion H; subst;
    eauto.
  Qed.


  Definition immediate_subterm t0 t := 
      exists k1 k2 (ec : elem_context_kinded k1 k2), t = ec:[t0].

  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.



  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.
  Notation decomp'   := (@decomp ()).


  Definition dec (t : term) k (d : decomp k) : Prop := 
      t = d.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End MiniML_PreRefSem.




Module MiniML_Strategy <: REF_STRATEGY MiniML_PreRefSem.

  Import MiniML_PreRefSem.


  Inductive elem_dec k : Set :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.

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


  Lemma dec_term_correct :                                                    forall t k,
      match dec_term t k with
      | ed_red r      => t = r
      | ed_val v      => t = v
      | ed_dec _ t' ec => t = ec:[t']
      end.

  Proof with auto.
    destruct k, t; simpl... 
  Qed.


(*  Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
  Proof.
    intros ? k H.
    inversion H.
  Qed. 


  Lemma dec_term_next_alive : 
      forall t k t0 ec0, dec_term t k = ed_dec t0 ec0 -> ~ dead_ckind (k+>ec0).

  Proof. auto. Qed. *)


  Lemma dec_context_correct :            forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r      => ec:[v] = r
      | ed_val v'     => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.

  Proof.
    intros k ec v.
    destruct k, ec; dependent destruction v;
    simpl;
    solve [ auto ].
  Qed.


(*  Lemma dec_context_from_dead : forall ec k v, 
      dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

  Proof.
    intros ec k v H.
    inversion H.
  Qed.


  Lemma dec_context_next_alive : forall ec k v {t ec0}, 
      dec_context ec k v = ed_dec t ec0 -> ~ dead_ckind (k+>ec0).

  Proof. auto. Qed. *)


  Inductive elem_context_in k : Set :=
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
