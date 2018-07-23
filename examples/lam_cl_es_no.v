Require Import Program
               Util
               refocusing_semantics.



Open Scope list.


Module Lam_ClES_NO_PreRefSem <: PRE_REF_SEM.

  Require Export Peano_dec Compare_dec.


  Inductive term0 :=
  | Var0   : nat            -> term0
  | Lam0   : term0          -> term0
  | App0   : term0 -> term0 -> term0.


  Inductive closure : Set :=
  | Cl : term0 -> list (nat * substitut) -> closure

  with substitut : Set :=
  | Sub   : closure -> substitut
  | Shift : nat     -> substitut.

  Notation env     := (list (nat * substitut)).
  Notation "t @ s" := (Cl t s) (at level 10).


  Inductive term' : Set := 
  | Var   : nat               -> term'
  | Lam   : term'             -> term'
  | App   : term' -> term'    -> term'
  | Cl_t  : closure           -> term'
  | OpVar : nat -> env -> nat -> term'.
  Definition term := term'.
  Hint Unfold term.


  Fixpoint term0_to_term t0 : term :=
      match t0 with 
      | Var0 i     => Var i 
      | Lam0 t     => Lam (term0_to_term t) 
      | App0 t1 t2 => App (term0_to_term t1) (term0_to_term t2) 
      end.
  Coercion term0_to_term : term0 >-> term.

  Coercion closure_to_term cl : term := Cl_t cl.


  Inductive ck := C | ECa.
  Definition ckind := ck.
  Hint Unfold ckind.


(*  Ltac destruct_all_CECa :=
      repeat match goal with H : CECa ?k |- _ => 
          try destruct k; destruct H
      end. *)


  Definition init_ckind : ckind     :=  C.
(*  Definition dead_ckind (k : ckind) :=  k = CBot.
  Hint Unfold init_ckind dead_ckind. *)


  Inductive val : ckind -> Type :=

  | vCLam   : val C           -> val C
  | vCVar   : nat             -> val C
  | vCApp   : valCa -> val C  -> val C

  | vECaLam    : term         -> val ECa
  | vECaLam_cl : term0 -> env -> val ECa
  | vECaCa     : valCa        -> val ECa

  with valCa :=

  | vCaVar : nat            -> valCa
  | vCaApp : valCa -> val C -> valCa.

  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val   Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.


  Fixpoint valueC_to_term0 (v : value C) : term0 :=
      match v with
      | vCLam v     => Lam0 (valueC_to_term0 v) 
      | vCVar i     => Var0 i
      | vCApp v1 v2 => App0 (valCa_to_term0 v1) (valueC_to_term0 v2)
      end

  with valCa_to_term0 v : term0 :=
      match v with
      | vCaVar i     => Var0 i
      | vCaApp v1 v2 => App0 (valCa_to_term0 v1) (valueC_to_term0 v2)
      end.
  Coercion valCa_to_term0 : valCa >-> term0.


  Definition value_to_term {k} : value k -> term :=
      match k as k return value k -> term with
      | C    => fun v => valueC_to_term0 v
      | ECa  => fun v => match v with
                         | vECaLam t      => Lam t
                         | vECaLam_cl t e => Cl (Lam0 t) e 
                         | vECaCa v'      => valCa_to_term0 v'
                         end
      end.
  Coercion value_to_term : value >-> term.


  (*Definition not_closure (t : term) := match t with Cl_t _ => False | _ => True end.*)

  Inductive red : ckind -> Type :=
  | rAppLam    : forall k, term         -> term         -> red k
  | rAppLam_cl : forall k, term0 -> env -> term         -> red k

  | rSubVar    : forall k, nat            -> env        -> red k
  | rSubOpVar  : forall k, nat            -> env -> nat -> red k
  | rSubLam    :           term0          -> env        -> red C
  | rSubApp    : forall k, term0 -> term0 -> env        -> red k.
  Definition redex := red.
  Hint Unfold redex.


  Definition redex_to_term {k} (r : redex k) : term := 
      match r with
      | rAppLam _ t1 t2       => App (Lam t1) (t2 : term)
      | rAppLam_cl _  t0 e t2 => App (Cl (Lam0 t0) e : term) t2

      | rSubVar _ i     e     => Cl (Var0 i) e
      | rSubOpVar _ i e g     => OpVar i e g
      | rSubLam     t0    e   => Cl (Lam0 t0) e
      | rSubApp _ t1 t2 e     => Cl (App0 t1 t2) e
      end.
  Coercion redex_to_term : redex >-> term.


  (*Lemma init_ckind_alive : ~dead_ckind init_ckind.
  Proof. auto. Qed.*)


  Inductive eck : ckind -> ckind -> Set :=
  | lam_c : eck C C
  | ap_r  : forall {k}, term  -> eck k ECa
  | ap_l  : forall {k}, valCa -> eck k C.
  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.


  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | lam_c   => Lam t
      | ap_r cl => App t (cl : term)
      | ap_l v  => App (v : term) t
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


(*  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | C    => match ec with lam_c => C    | ap_r _ => ECa | ap_l _ => C end
      | ECa  => match ec with lam_c => CBot | ap_r _ => ECa | ap_l _ => C end
      | CBot => CBot
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).*)


(*  Lemma death_propagation : 
      forall k ec, dead_ckind k -> dead_ckind (k+>ec).

  Proof.
    intros k ec H.
    destruct k;
    inversion H;
    reflexivity.
  Qed.


  Lemma proper_death : forall k, dead_ckind k -> ~ exists (r : redex k), True.
  Proof.
    intros k H [r _].
    destruct r; destruct_all_CECa; 
    solve [inversion H].
  Qed.*)


  Inductive context (k1 : ckind) : ckind -> Type :=
  | empty : context k1 k1
  | ccons :                                                                forall {k2 k3}
            (ec : elem_context_kinded k2 k3), context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1 k2 k3} _ _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).


  Lemma term0_to_term_injective : 
      forall t t', term0_to_term t = term0_to_term t' -> t = t'.

  Proof.
    induction t; intros t' H; 
    destruct t'; inversion H; 
    solve [ f_equal; auto ].
  Qed.


  Lemma closure_to_term_injective :
      forall cl cl', closure_to_term cl = closure_to_term cl' -> cl = cl'.

  Proof. inversion 1; auto. Qed.

(*
  Lemma value_C_to_term_is : 
      forall v : value C, value_to_term v = term0_to_term (valueC_to_term0 v).

  Proof. dependent destruction v; auto. Qed.*)


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa, valCa_to_term0 v = valCa_to_term0 v' -> v = v');
        dependent destruction v'; 
        intro H; inversion H;
        simpl in *;

    match goal with 
    | _ => solve [auto using f_equal, f_equal2, term0_to_term_injective]
    | v : valCa |- _ => destruct v; discriminate
    end.
  Qed.


  Lemma valCa_to_term0_injective : 
      forall v v', valCa_to_term0 v = valCa_to_term0 v' -> v = v'.

  Proof.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa, valCa_to_term0 v = valCa_to_term0 v' -> v = v');
        dependent destruction v'; 
        intro H; inversion H;
        simpl in *;

    match goal with 
    | _ => solve [auto using f_equal, f_equal2, term0_to_term_injective]
    | v : valCa |- _ => destruct v; discriminate
    end.
  Qed.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    intros k r r' H.
    destruct k;
    dependent destruction r; dependent destruction r';
    inversion H; subst;

    repeat match goal with 
(*    | H : CECa ?k |- _ => 
          try destruct k; destruct H*)
    | H : _ ++ _ :: _ = _ ++ _ :: _ |- _ =>
          destruct (List.app_inj_tail _ _ _ _ H) as (?, G);
          inversion G
    end;

    try solve [ f_equal; auto | destruct_all closure; autof |
destruct t1, t2; destruct n0, n; autof ].
  Qed.


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    solve
    [ inversion H; trivial ].
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec {k1 k2} (ec : elem_context_kinded k1 k2) t := 
      exists t', ec:[t'] = t.


  Definition sub_step i j s e g :=
      if lt_dec i j then Var (i+g) else
      match s with
      | Sub (Cl t e') => if eq_nat_dec i j then Cl t ((0, Shift (g+j))::e') : term
                                           else OpVar (i-j-1) e (g+j)
      | Shift g'      => OpVar (i-j) e (g+j+g')
      end.


  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rAppLam    _ _ _            => None 
      | rAppLam_cl _ t e (Cl_t cl)  => Some (Cl t ((0, Sub cl)::e) : term)
      | rAppLam_cl _ t e _          => None
      | rSubVar _ i ([])            => Some (Var i)
      | rSubVar _ i ((j, s)::e)     => Some (sub_step i j s e 0)
      | rSubOpVar _ i ([]) g        => Some (Var (i+g))
      | rSubOpVar _ i ((j, s)::e) g => Some (sub_step i j s e g)
      | rSubLam t ([])              => Some (Lam (Cl t ([]) : term))
      | rSubLam t ((j, s)::e)       => Some (Lam (Cl t ((1+j, s)::e) : term))
      | rSubApp _ t1 t2 e           => Some (App (Cl t1 e : term) (Cl t2 e : term))
      end.


  Lemma valCa_is_valECa : 
      forall v1 : valCa, exists v2 : value ECa,  value_to_term v2 = valCa_to_term0 v1.

  Proof with auto.
    destruct v1; intros.
    - exists (vECaCa (vCaVar n))...
    - exists (vECaCa (vCaApp v1 v))...
  Qed.


  Lemma value_trivial1 :
      forall {k1 k2} (ec:elem_context_kinded k1 k2) t,
          forall v : value k1,  ec:[t] = v ->
              exists (v' : value k2), t = v'.

  Proof.
    intros k1 k2 ec t v H.
    destruct ec; dependent destruction v;
        try match goal with H : _ = _ (vECaCa ?v) |- _ => destruct v end;
        inversion H; subst; 
    solve 
    [ simpl; eautof
    | eexists (vECaCa _); simpl; eauto ].
  Qed.


  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof with auto.
    intros k k' r ec t H.
    destruct ec; dependent destruction r; inversion H; subst;
    solve 
    [ eexists (vECaLam _); reflexivity
    | eexists (vECaLam_cl _ _); reflexivity 
    | match goal with H: _ (valCa_to_term0 ?v) = ?r |- _ => 
          destruct v; inversion H 
      end].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.

  Proof.
    intros k v r H.

    dependent destruction r; dependent destruction v; 
    inversion H;
    repeat match goal with 
    | H : _ (valCa_to_term0 ?v) = _ |- _ => destruct v; inversion H
    end.
  Qed.


  Inductive decomp k : Type :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition dec (t : term) k (d : decomp k) : Prop :=
      t = d.


  Definition immediate_subterm t0 t := exists k1 k2 (ec : elem_context_kinded k1 k2),
      t = ec:[t0].

  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.


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

End Lam_ClES_NO_PreRefSem.




Module Lam_ClES_NO_Strategy <: REF_STRATEGY Lam_ClES_NO_PreRefSem.

  Import Lam_ClES_NO_PreRefSem.


  Inductive elem_dec k : Type :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.    Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.


  Definition dec_term t k : elem_dec k :=

      match k as k0 return elem_dec k0 with 
      | C    => match t with
                | App t1 t2   => ed_dec _ t1 (ap_r t2)
                | Var i       => ed_val (vCVar i)
                | Lam t1      => ed_dec _ t1 lam_c
                | Cl_t (Cl (Var0 i) e)     => ed_red (rSubVar C i e)
                | Cl_t (Cl (Lam0 t) e)     => ed_red (rSubLam t e)
                | Cl_t (Cl (App0 t1 t2) e) => ed_red (rSubApp C t1 t2 e)
                | OpVar i e g => ed_red (rSubOpVar C i e g)
                end
      | ECa  => match t with
                | App t1 t2 => ed_dec _ t1 (ap_r t2)
                | Var i     => ed_val (vECaCa (vCaVar i))
                | Lam t1    => ed_val (vECaLam t1)
                | Cl_t (Cl (Var0 i) e)     => ed_red (rSubVar ECa i e)
                | Cl_t (Cl (Lam0 t) e)     => ed_val (vECaLam_cl t e)
                | Cl_t (Cl (App0 t1 t2) e) => ed_red (rSubApp ECa t1 t2 e)
                | OpVar i e g   => ed_red (rSubOpVar ECa i e g)
                end
      end.


  Program Definition dec_context
          {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k :=

      match ec in eck k k' return val k' -> elem_dec k with

      | lam_c      => fun v => ed_val (vCLam v)
(*      | lam_c, ECa    => fun _ => _*)
(*      | lam_c, CBot   => fun _ => in_dead*)

      | @ap_r k t     => fun v =>
                             match v in val k' return k' = ECa -> elem_dec k with
                             | vECaLam t0      => fun _ => ed_red (rAppLam k t0 t)
                             | vECaLam_cl t0 e => fun _ => ed_red (rAppLam_cl k t0 e t)
                             | vECaCa v        => fun _ => ed_dec _ t (ap_l v)
                             | _ => _
                             end eq_refl
(*      | ap_r t    => fun v =>
                             match v with
                             | vECaLam t0      => ed_red (rAppLam ECa t0 t)
                             | vECaLam_cl t0 e => ed_red (rAppLam_cl ECa t0 e t)
                             | vECaCa v        => ed_dec _ t (ap_l v)
                             (*| _ => @in_dead ECa*)
                             end*)
(*      | ap_r t, CBot  => fun _ => in_dead*)

      | @ap_l k v0 => fun v => match k with 
                               | C => ed_val (vCApp v0 v)
                               | ECa => ed_val (vECaCa (vCaApp v0 v))
                               end
      (*  | ap_l v0, CBot => fun _ => in_dead*)

      end v.


  Lemma dec_term_correct :                                           forall (t : term) k,
      match dec_term t k with
      | ed_red r      => t = r
      | ed_val v      => t = v
      | ed_dec _ t' ec => t = ec:[t']
      end.

  Proof.
    destruct k, t; 
    try match goal with c : closure |- _ => 
        destruct c as [t0]; destruct t0 
    end; 
    solve [ simpl; auto ].
  Qed.


(*  Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
  Proof.
    intros t k H.
    destruct k;
    solve [ autof ].
  Qed.


  Lemma dec_term_next_alive : 
      forall t k t0 ec0, dec_term t k = ed_dec t0 ec0 -> ~ dead_ckind (k+>ec0).

  Proof.
    intros t k t0 ec0 H.

    destruct t, k;
    try match goal with c : closure |- _ => 
        destruct c as [tt0]; destruct tt0 
    end;
        inversion H; subst; 

    solve [ auto ].
  Qed.*)


  Lemma dec_context_correct :            forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r      => ec:[v] = r
      | ed_val v'     => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.

  Proof.
    intros k k' ec v.
    destruct k; dependent destruction ec; dependent destruction v;
    simpl;
    try solve [ auto ].
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
      | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
      | _, _           => False
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
    intros k t [? ec0] [? ec1] [? ec2] H H0.
    destruct k; dependent destruction ec0; dependent destruction ec1;
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
    destruct k; dependent destruction ec0; dependent destruction ec1;
    inversion H5; subst;

    solve
    [ compute; eautof 7
    | do 2 right;
      apply term0_to_term_injective  in H0;
      apply valCa_to_term0_injective in H0;
      subst;
      auto ].
  Qed.


  Lemma search_order_comp_fi :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

       k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t.

  Proof with auto.
    intros t k k' k'' ec0 ec1 H.
    destruct k; dependent destruction ec0; dependent destruction ec1;
    inversion H;
    solve [auto].
  Qed.


  Lemma dec_term_term_top :                                             forall k k' t t',

       forall (ec : elem_context_kinded k k'),
           dec_term t k = ed_dec _ t' ec -> so_maximal ec t.

  Proof.
    intros k k' t t' ec H ec' H0.
    destruct k, t; dependent destruction ec'; 
    destruct_all closure;
    try match goal with t0 : term0 |- _ => destruct t0 end;
    try solve [ inversion H; dep_subst; inversion H0 ].
  Qed.


  Lemma dec_context_red_bot :                   forall k k' (v : value k') (r : redex k),

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].

  Proof.
    intros k k' v r ec H [? ec'] H0.
    destruct k;
    dependent destruction ec; dependent destruction ec';
    dependent destruction v;
    solve
    [ autof
    | inversion H;
      dep_subst;
      unfold search_order in H0; destruct H0 as (H0, _);
      destruct H0 as (t1, H0); inversion H0; subst;
      destruct v0; 
      autof ].
  Qed.


  Lemma dec_context_val_bot :                               forall k k' v {v' : value k},

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_val v' -> so_minimal ec ec:[v].

  Proof.
    intros k k' v v' ec H [? ec'].
    destruct k;
    dependent destruction ec; dependent destruction ec';
    dependent destruction v;
    try solve [ autof ].
  Qed.


  Lemma dec_context_term_next :                                      forall k0 k1 k2 v t,

      forall (ec0 : elem_context_kinded k0 k1) (ec1 : elem_context_kinded k0 k2),
          dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros k0 k1 k2 v t ec0 ec1 H.
    destruct k0;
    dependent destruction ec0; dependent destruction ec1;
    dependent destruction v;
    try solve
    [ autof

    | inversion H; dep_subst;
      split;
      [ constructor; 
        compute; eauto
      | intros [? ec''] H0 H1; 
        dependent destruction ec'';
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
    unfold search_order in H; destruct H as (H, G).

    exists (vECaCa v).
    inversion H as (t1, H1).
    subst.
    inversion G as [t2 G2].
    inversion G2.
    trivial.
  Qed.

End Lam_ClES_NO_Strategy.


Module Lam_ClES_NO_RefSem := RedRefSem Lam_ClES_NO_PreRefSem Lam_ClES_NO_Strategy.



Require Import refocusing_machine.

Module Lam_ClES_NO_EAM := RefEvalApplyMachine Lam_ClES_NO_RefSem.


(*
Require Import abstract_machine.

Module Lam_ClES_NO_EAM_safe <: AM_SAFE_REGION Lam_ClES_NO_EAM.

  Import Lam_ClES_NO_EAM.
  Import Lam_ClES_NO_RefLang.



  Fixpoint good_context {k1 k2} (c : context k1 k2) :=
      match c with
      | [.]                 => True
      | ap_r (Cl_t _) =: c' => good_context c'
      |        ap_r _ =: _  => False
      |             _ =: c' => good_context c'
      end.

  Fixpoint good_term t k := 
      match t with
      | Cl_t _                => True
      | App (Cl_t _) (Cl_t _) => True
      | Var _                 => True
      | Lam t                 => C = k /\ good_term t C
      | OpVar _ _ _           => True
      | _                     => False
      end.

  Definition good_value {k} (v : value k) :=
      match v with
      | vECaLam _ => False
      | _ => True
      end.

  Definition safe (st : configuration) :=
      match st with
      | c_eval t k1 k2 c  => good_term t k2 /\ good_context c /\ 
                             k1 = init_ckind /\ k2 <> CBot
      | c_apply k1 k2 c v => good_value v /\ good_context c /\ 
                             k1 = init_ckind /\ k2 <> CBot
      end.


  Lemma sub_step_good : forall i j s e g k, good_term (sub_step i j s e g) k.
  Proof.
    intros.
    unfold sub_step.
    destruct (lt_dec i j).
    - simpl; auto.
    - destruct s as [[t e'] | g'].
      + destruct (eq_nat_dec i j).
        * simpl; auto.
        * simpl; auto.
      + simpl; auto.
  Qed.


  Lemma preservation : forall st1 st2, safe st1 -> st1 → st2 -> safe st2.

  Proof.
    intros st1 st2 H H0.
    destruct H0; try destruct H.
    
    - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
      try destruct tt1, tt2;
      inversion H; subst;
      try discriminate;
      inversion H0; subst. 
      + destruct l as [ | (?, ?) ?]; inversion H1. 
        * simpl; auto.
        * simpl; intuition.
          auto using sub_step_good.
      + destruct l as [ | (?, ?) ?]; inversion H1. 
        * simpl; auto.
        * simpl; intuition.
          auto using sub_step_good.
      + destruct l as [ | (?, ?) ?]; inversion H1.
        * simpl; auto.
        * simpl; auto.
      + inversion H1; simpl; auto.
      + inversion H1; simpl; auto.
      + destruct l as [ | (?, ?) ?]; inversion H1. 
        * simpl; auto.
        * simpl; intuition.
          auto using sub_step_good.
      + destruct l as [ | (?, ?) ?]; inversion H1. 
        * simpl; auto.
        * simpl; intuition.
          auto using sub_step_good.
    - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
      try destruct tt1, tt2;
      inversion H; subst;
      inversion H0; subst; 
      simpl; intuition.
    - destruct t as [? | ? | tt1 tt2 | [[? | ? | ? ?] ?] | ?], k2;
      try destruct tt1, tt2;
      inversion H; subst;
      try discriminate;
      inversion H0; subst.
      + simpl in *; intuition.
      + simpl; intuition.
      + simpl; auto.
    - destruct ec0, k2; dependent destruction v; 
      inversion H0; subst; autof.
      + destruct t0; inversion H1; subst. simpl; intuition.
      + destruct t0; inversion H1; subst. simpl; intuition.
    - destruct ec0 as [ | tt | ? ], k2; destruct tt; simpl in H;
      dependent destruction v; 
      inversion H0; simpl in *; intuition. 
    - destruct ec0, k2; dependent destruction v;
      inversion H0; subst.
      + destruct t; simpl in *; intuition.
      + destruct t; simpl in *; intuition.
  Qed.


  Lemma progress : forall st, safe st -> 
                       (exists v, st = c_final v) \/ (exists st', st → st').
  Proof.
    intros.
    destruct st.
    - right. 
      destruct t as 
          [? | ? | tt1 tt2 | [[? | ? | ? ?] [ | (?, ?) ?]] | ? [ | (?, ?) ?] ?], 
          k2;
      try destruct tt1, tt2;

      destruct H as [? [? ?]];
      inversion H; try solve [intuition];

      eexists; try solve [ apply t_val; simpl; intuition
                         | apply t_term; simpl; intuition
                         | eapply t_red; simpl; intuition].
    - destruct c.
      + left. 
        simpl in H; rec_subst H. 
        dependent destruction v;
        eauto.
      + right. 
        destruct ec0 as [ | tt | ?], k2; dependent destruction v;
        destruct tt;
        destruct H as [? [? ?]]; try destruct H0; try destruct H;
        eexists; try solve [ apply t_cval; simpl; auto 
                           | eapply t_cred; [simpl; auto | simpl; auto] 
                           | apply t_cterm; simpl; auto].
  Qed.

End Lam_ClES_NO_EAM_safe.




Module Lam_ClES_NO_EAM_minus <: DET_ABSTRACT_MACHINE.

  Module AM := Lam_ClES_NO_EAM.
  Import Lam_ClES_NO_RefLang.

  Definition term := term0.
  Definition value := AM.value.
  Definition configuration := AM.configuration.
  Definition c_init (t : term0) := AM.c_init (Cl_t (Cl t nil)). (*!*)
  Definition c_final := AM.c_final.
  Definition final_correct := AM.final_correct.
  Definition transition := AM.transition.
  Notation "c1 → c2" := (transition c1 c2) (at level 40, no associativity).

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

  Definition next_conf    := AM.next_conf.
  Definition next_correct := AM.next_correct.

End Lam_ClES_NO_EAM_minus.




Require Import abstract_machine_facts.

Module Lam_ClES_NO_EAM_minus_InitSafe <: 
           AM_INIT_SAFE  Lam_ClES_NO_EAM_minus  Lam_ClES_NO_EAM_safe.

  Import Lam_ClES_NO_EAM_minus Lam_ClES_NO_EAM_safe.

  Lemma init_safe : forall t, safe (c_init t).
  Proof. simpl; auto. Qed.

End Lam_ClES_NO_EAM_minus_InitSafe.




Module Lam_ClES_NO_EAM_minus_Progress <: AM_PROGRESS Lam_ClES_NO_EAM_minus :=

    AM_ProgressFromSafety  Lam_ClES_NO_EAM_minus  Lam_ClES_NO_EAM_safe
                           Lam_ClES_NO_EAM_minus_InitSafe.
*)

