(* Addition with left-to-right reduction strategy *)

Require Import Program
               Util
               refocusing_semantics.

Module Addition_PreRefSem <: PRE_REF_SEM.

  Inductive expr :=
  | Const : nat -> expr
  | Plus : expr -> expr -> expr.
  Definition term := expr.
  Coercion Const : nat >-> expr.
  Hint Unfold term.

  Definition ckind : Type := ().
  Hint Unfold  ckind.

  Inductive val : ckind -> Type :=
  | Value : nat -> val ().

  Definition value := val.
  Hint Unfold value.

  Definition value_to_term {k} (v : value k) : term :=
    match v with
    | Value n => Const n
    end.

  Inductive red : ckind -> Type :=
  | Addition : value () -> value () -> red ().
  Definition redex := red.
  Hint Unfold redex.

  Definition redex_to_term {k} (r : redex k) : term :=
    match r with
    | Addition n m => Plus (value_to_term n) (value_to_term m)
    end.

  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Proof.
    intros k [v] v' H.
    dependent destruction v'.
    inversion H.
    reflexivity.
  Qed.

  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.
  Proof.
    intros k [r] r' H.
    dependent destruction r'.
    inversion H.
    apply value_to_term_injective in H1.
    apply value_to_term_injective in H2.
    subst.
    reflexivity.
  Qed.

  Inductive eck : ckind -> ckind -> Type :=
  | left_hole   : term     -> eck () ()
  | right_hole  : value () -> eck () ().

  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  Definition init_ckind : ckind :=  ().

  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
    match ec with
    | left_hole t' => Plus t t'
    | right_hole v => Plus (value_to_term v) t
    end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.
  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    inversion H; trivial.
  Qed.

  Definition contract {k} (r : redex k) : option term :=
    match r with
    | Addition (Value n) (Value m) => Some (Const (n + m))
    end.

  Include RED_SEM_BASE_Notions.

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
    intros ? ? ec t [v] H.
    destruct ec; inversion H.
  Qed.

  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof. intros k [v] [r] H. inversion H. Qed.

  Lemma redex_trivial1 : forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.
  Proof.
    intros ? ? [r] [|] t0 H;
    inversion H;
    eexists;
    reflexivity.
  Qed.

End Addition_PreRefSem.

Module Addition_Strategy <: REF_STRATEGY Addition_PreRefSem.

  Import Addition_PreRefSem.

  Inductive elem_dec k : Type :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.

  Definition dec_term (t : expr) (k : ckind) : elem_dec k :=
  match k with () =>
    match t with
    | Const n    => ed_val (Value n)
    | Plus t1 t2 => ed_dec () t1 (left_hole t2)
    end
  end.

  Lemma dec_term_correct :
    forall (t : term) k, match dec_term t k with
                         | ed_red r      => t = r
                         | ed_val v      => t = v
                         | ed_dec _ t' ec => t = ec:[t']
                         end.
  Proof. intros [|] []; simpl; auto. Qed.

  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec with
    | left_hole t   => fun v => ed_dec () t (right_hole v)
    | right_hole v' => fun v => ed_red (Addition v' v)
    end v.

  Lemma dec_context_correct :         forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r        => ec:[v] = r
      | ed_val v'       => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.
  Proof. intros ? ? [|] ?; simpl; auto. Qed.

  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop :=
    let (_, ec)  := ec  in
    let (_, ec0) := ec0 in
    match ec, ec0 with
    | right_hole _, left_hole _ => immediate_ec ec t /\ immediate_ec ec0 t
    | _, _ => False
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

  Lemma elem_context_det :         forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
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
   exists (Value n). reflexivity.
 Qed.

End Addition_Strategy.

Module Addition_RefSem := RedRefSem Addition_PreRefSem Addition_Strategy.



Require Import refocusing_machine.

Module Addition_EAM := RefEvalApplyMachine Addition_RefSem.

Import Addition_PreRefSem.

Import Addition_EAM.

Require Import abstract_machine_facts.
Module Addition_sim := DetAbstractMachine_Sim Addition_EAM.
Import Addition_sim.

Fixpoint list_configs c n i :=
 match n with
 | 0 => nil
 | S n' =>  match c with
            | None => nil
            | Some c' => cons (i,c')  (list_configs (n_steps c' 1) n' (S i))
            end
 end.

Fixpoint list_configurations t n := list_configs (Some (load t)) n 1.

Definition t := (Plus (Plus 1 2) (Plus 4 8)).

Eval compute in list_configurations t 17.

(*
[( 1 + 2 ) + ( 4 + 8 )]
[[ 1 + 2 ] + ( 4 + 8 )]
[[[1]+ 2 ] + ( 4 + 8 )]
[[[ ]+ 2 ] + ( 4 + 8 )] 1
[[ 1 +[2]] + ( 4 + 8 )]
[[ 1 +[ ]] + ( 4 + 8 )] 2
[[   3   ] + ( 4 + 8 )]
[[       ] + ( 4 + 8 )] 3
[    3     + [ 4 + 8 ]]
[    3     + [[4]+ 8 ]]
[    3     + [[ ]+ 8 ]] 4
[    3     + [ 4 +[8]]]
[    3     + [ 4 +[ ]]] 8
[    3     + [   C   ]]
[    3     + [       ]] C
[          F          ]
[                     ] F
*)

