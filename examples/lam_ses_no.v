

(* Lambda calculus with normal order and simple explicit substitutions example *)


Require Import Program
               Util
               refocusing_semantics.

(* Here we define the reduction semantics. *)
(* The module type PRE_REF_SEM is defined in  the file refocusing/refocusing_semantics.v *)
(* It inherits part of the signature from RED_SEM defined in reduction_semantics/reduction_semantics.v *)

Module Lam_SES_NO_PreRefSem <: PRE_REF_SEM.

  Require Export Peano_dec Compare_dec.


  (* The first parameter required by RED_SEM is the set of terms. *)
  (* Here we define the language of interest: lambda calculus. *)
  (* In Coq it is not possible to define parameter of a module *)
  (* as an inductive type, therefore we first define inductively *)
  (* term' and only then we define terms as term'. *)

  Inductive term' :=
  | Var   : nat                   -> term'
  | Lam   : term'                 -> term'
  | App   : term' -> term'        -> term'
  | Sub   : term' -> nat -> term' -> term'
  | Shift : term' -> nat -> nat   -> term'.
  Definition term := term'.

  (* The main ingredient of a reduction semantics is a grammar of contexts.  *)
  (* We start with nonterminal symbols, which are called here "context kinds". *)
  (* In normal order we need two nonterminals: Eᵏ (this one goes under
  lambdas) and Fᵏ (which does not allow to go under lambda). Here we
  have not only normal order, but also simple explicit substitutions,
  and thus we need the third nonterminal Dᵏ to traverse these
  substitutions *)

  Inductive ck := Eᵏ | Fᵏ | Dᵏ.
  Definition ckind := ck.
  Hint Unfold ckind.

  (* Nonterminals Eᵏ and Fᵏ are quite similar and often we want to
  treat them together *)
  Inductive EF_kind := Eᵏ' | Fᵏ'.
  Coercion EFk2ckind (k : EF_kind) : ckind :=
      match k with Eᵏ' => Eᵏ | Fᵏ' => Fᵏ end.

  (* starting symbol in the grammar of contexts *)
  Definition init_ckind : ckind := Eᵏ.
  Hint Unfold init_ckind.

  (* Now we define (for each context kind) the set of values. *)
  (* For technical reasons we have to use fresh constructors; later we will *)
  (* use a coercion to identify values with the corresponding lambda terms. *)

  Inductive val : ckind -> Set :=

  | vELam : val Eᵏ -> val Eᵏ
  | vEVar : nat    -> val Eᵏ
  | vEApp : valCa  -> val Eᵏ -> val Eᵏ

  | vFLam : term   -> val Fᵏ
  | vFVar : nat    -> val Fᵏ
  | vFApp : valCa  -> val Eᵏ -> val Fᵏ

  | vDLam : term   -> val Dᵏ
  | vDVar : nat    -> val Dᵏ
  | vDApp : term   -> term -> val Dᵏ

  with valCa : Set :=

  | vEaVar : nat   -> valCa
  | vEaApp : valCa -> val Eᵏ -> valCa.

  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val   Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.

  (* The coercion is a simple function that changes occurrences of vLam constructors to Lam etc. *)

  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vELam v     => Lam (value_to_term v)
      | vEVar x     => Var x
      | vEApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vFLam t     => Lam t
      | vFVar x     => Var x
      | vFApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      | vDLam t0    => Lam t0
      | vDVar n     => Var n
      | vDApp t0 t1 => App t0 t1
      end

  with valCa_to_term v : term :=
      match v with
      | vEaVar x     => Var x
      | vEaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valCa_to_term : valCa >-> term.


  Definition vVar n k : value k :=
      match k with
      | Eᵏ => vEVar n | Fᵏ => vFVar n | Dᵏ => vDVar n
      end.


  Inductive esubstitute :=                 (* explicit substitutions: substitute and shift *)
  | st_sub   : term -> esubstitute
  | st_shift : nat  -> esubstitute.
  Definition esub := (nat * esubstitute)                                           %type.

  (* Here we define the set of potential redices. *)
  Inductive red : ckind -> Type :=
  | rEApp    : term -> term -> red Eᵏ
  | rFApp    : term -> term -> red Fᵏ
  | rSubVar  : forall k, nat          -> esub -> red k
  | rSubLam  : forall k, term         -> esub -> red k
  | rSubApp  : forall k, term -> term -> esub -> red k.
  Definition redex := red.
  Hint Unfold redex.

  (* Here comes the actual definition of the grammar of contexts. *)
  (* There are also a trivial productions such as  Eᵏ -> [] which are omitted here. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *)

  Inductive eck : ckind -> ckind -> Set :=
  | lam_c  : eck Eᵏ Eᵏ                                             (* E -> \lambda E *)
  | ap_r   : forall k : EF_kind, term  -> eck k Fᵏ     (* E -> F e ; F -> F e *)
  | ap_l   : forall k : EF_kind, valCa -> eck k Eᵏ     (* E -> a E ; F -> a E *)
  | esub_c : forall k : ckind,   esub  -> eck k Dᵏ.    (* E -> esub D ; F -> esub D; D -> esub D *)
  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | lam_c     => Lam t
      | ap_r _ t' => App t t'
      | ap_l _ v  => App (v : term) t
      | esub_c _ (j, st_sub t')  => Sub t j t'
      | esub_c _ (j, st_shift g) => Shift t j g
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

  (* Again we use a coercion to identify redices with the corresponding lambda terms. *)
  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rEApp t1 t2   => App (Lam t1) t2
      | rFApp t1 t2 => App (Lam t1) t2
      | rSubVar k' n d     => (esub_c k' d):[Var n]
      | rSubLam k' t d     => (esub_c k' d):[Lam t]
      | rSubApp k' t1 t2 d => (esub_c k' d):[App t1 t2]
      end.

  (* Here we define the contraction.  *)
  Definition contract0 {k} (r : redex k) : term :=
      match r with
      | rEApp   t0 t1 => Sub t0 0 t1
                 (*  in the E-substrategy the application  (t0 t1) reduces  to  t0[0->t1] *)
      | rFApp t0 t1 => Sub t0 0 t1
      | rSubVar _ i  (j, st_sub t)   => if lt_dec i j     then Var i else    (* i[j->t] ==> i *)
                                        if eq_nat_dec i j then Shift t 0 j               (* i[i->t] ==> t[0 v i] *)
                                                          else Var (pred i)                     (* i[j->t] ==> j-1 *)
      | rSubVar _ i  (j, st_shift g) => if lt_dec i j     then Var i
                                                          else Var (i+g)
      | rSubLam _ t  (j, d)          => Lam ((esub_c Eᵏ (S j, d)):[t])    (* substitution pushed under lambda  *)
      | rSubApp _ t1 t2 d            => App (esub_c Fᵏ d):[t1] (esub_c Eᵏ d):[t2]   (* substitution pushed under application *)
      end.
  Definition contract {k} (r : redex k) := Some (contract0 r).

  (* Having this we include some basic notions *)
  Include RED_SEM_BASE_Notions.

  (* Some technicalities: it should be obvious that the two coercions are injective *)
  (* This again is a required axiom in the signature of RED_SEM module *)
  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma valCa_to_term_injective :
      forall v v', valCa_to_term v = valCa_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;
    dependent destruction r; dependent destruction r';
    destruct_all esub; destruct_all esubstitute;
    inversion H; subst;
    f_equal.
  Qed.


  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    destruct_all esub; destruct_all esubstitute;
    solve
    [ inversion H; trivial ].
  Qed.


  Lemma valCa_is_valECa :
      forall v1 : valCa, exists v2 : value Fᵏ, valCa_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vFVar n)...
    - exists (vFApp v1 v)...
  Qed.

  (* Decomposition of a value cannot give a potential redex, it must give a value. *)
  Lemma value_trivial1 :
      forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
          forall v : value k1,  ec:[t] = v ->
              exists (v' : value k2), t = v'.

  Proof.
    intros ? ? ec t v H.
    destruct ec; dependent destruction v;
    destruct_all esub; destruct_all esubstitute; destruct_all EF_kind;
    subst;
    inversion H;
    solve
    [ eautof
    | auto using valCa_is_valECa ].
  Qed.


  (* A value is not a redex. *)
  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.

  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v;
    simpl;
    try match goal with
    | |- App (valCa_to_term ?v) _ <> _ => dependent_destruction2 v
    end;
    destruct_all esub; destruct_all esubstitute;

    solve [ discriminate | tauto ].
  Qed.

  (* There are no other (potential) redices inside a redex; there can be only values. *)
  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof.
    intros ? ? r ec t H.
    destruct ec; dependent destruction r;
    destruct_all esub; destruct_all esubstitute; destruct_all EF_kind;
    subst;
    try discriminate;
    inversion H;
    try solve
    [ eexists (vFLam _); simpl; eauto
    | eexists (vELam _); simpl; eauto
    | eexists (vDLam _); simpl; eauto
    | eexists (vFApp _ _); simpl; eauto
    | eexists (vEApp _ _); simpl; eauto
    | eexists (vDApp _ _); simpl; eauto
    | eexists (vFVar _); simpl; eauto
    | eexists (vEVar _); simpl; eauto
    | eexists (vDVar _); simpl; eauto
    | match goal with v: valCa |- _ => destruct v; discriminate end ].
  Qed.

  (* The immediate subterm relation  is well-founded.  *)
  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof.
    REF_LANG_Help.prove_st_wf;

    solve (*rest with*)
    [ destruct_all esub; destruct_all esubstitute;
      inversion H1; subst;
      auto ].
  Qed.


  (* Subterm order is a well-founded relation. *)
  Definition wf_subterm_order : well_founded subterm_order
      := wf_clos_trans_l _ _ wf_immediate_subterm.

End Lam_SES_NO_PreRefSem.



(* Although a reduction semantics implicitly contains reduction strategy, our implementation
   requires an explicit definition of this strategy. So now we define the reduction strategy.  *)


(* The module type REF_STRATEGY is defined in the file refocusing/refocusing_semantics.v. *)
Module Lam_SES_NO_Strategy <: REF_STRATEGY Lam_SES_NO_PreRefSem.

  Import Lam_SES_NO_PreRefSem.
  Include RED_STRATEGY_STEP_Notions Lam_SES_NO_PreRefSem.


  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)
  Definition dec_term (t : term) (k : ckind) : elem_dec k :=

      match k as k0 return elem_dec k0 with
      | Eᵏ   => match t with
                | App t1 t2 => ed_dec _ t1 (ap_r Eᵏ' t2)
                | Var n     => ed_val (vEVar n)
                | Lam t1    => ed_dec _ t1 lam_c
                | Sub t1 n t2   => ed_dec _ t1 (esub_c Eᵏ (n, st_sub t2))
                | Shift t1 n t2 => ed_dec _ t1 (esub_c Eᵏ (n, st_shift t2))
                end
      | Fᵏ  => match t with
                | App t1 t2 => ed_dec _ t1 (ap_r Fᵏ' t2)
                | Var n     => ed_val (vFVar n)
                | Lam t1    => ed_val (vFLam t1)
                | Sub t1 n t2   => ed_dec _ t1 (esub_c Fᵏ' (n, st_sub t2))
                | Shift t1 n t2 => ed_dec _ t1 (esub_c Fᵏ' (n, st_shift t2))
                end
      | D    => match t with
                | App t1 t2 => ed_val (vDApp t1 t2)
                | Var n     => ed_val (vDVar n)
                | Lam t1    => ed_val (vDLam t1)
                | Sub t1 n t2   => ed_dec _ t1 (esub_c Dᵏ (n, st_sub t2))
                | Shift t1 n t2 => ed_dec _ t1 (esub_c Dᵏ (n, st_shift t2))
                end
      end.

  (* Here is the up-arrow function. *)
  (* It is used to decompose a context.  *)

  (* Here we would like to define this function as follows.


  Definition dec_context
          {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k :=

      match ec with

      | lam_c    => ed_val (vELam v)

      | ap_r k t   =>  match k with

                       | Eᵏ' => match v with
                                | vFLam t0    => ed_red (rEApp t0 t)
                                | vFVar n     => ed_dec _ t (ap_l Eᵏ' (vEaVar n))
                                | vFApp v1 v2 => ed_dec _ t (ap_l Eᵏ' (vEaApp v1 v2))
                                end
                       | Fᵏ' => match v  with
                                | vFLam t0    => ed_red (rFApp t0 t)
                                | vFVar n     => ed_dec _ t (ap_l Fᵏ' (vEaVar n))
                                | vFApp v1 v2 => ed_dec _ t (ap_l Fᵏ' (vEaApp v1 v2))
                                end
                       end

      | ap_l k0 v0  =>  match k0 with
                        | Eᵏ' => ed_val (vEApp v0 v)
                        | Fᵏ' => ed_val (vFApp v0 v)
                        end

      | esub_c k0 d =>  match v with
                        | vDLam t0    => ed_red (rSubLam _ t0 d)
                        | vDVar n     => ed_red (rSubVar _ n  d)
                        | vDApp t1 t2 => ed_red (rSubApp _ t1 t2 d)
                        end
      end v.

  Unfortunately, Coq is not able to infer equalities  like  k'=Eᵏ, and
  we have to do some dirty tricks.  *)



  Program Definition dec_context
          {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k :=

      match ec in eck k k' return value k' -> elem_dec k with

      | lam_c    => fun v => ed_val (vELam v)

      | ap_r k t   => fun (v : value Fᵏ) =>
                        match k as k return elem_dec k with
                        | Eᵏ' => match v in val k0 return k0 = Fᵏ -> elem_dec Eᵏ with
                                 | vFLam t0    => fun _ => ed_red (rEApp t0 t)
                                 | vFVar n     => fun _ => ed_dec _ t (ap_l Eᵏ' (vEaVar n))
                                 | vFApp v1 v2 => fun _ => ed_dec _ t (ap_l Eᵏ' (vEaApp v1 v2))
                                 | _ => _
                                 end eq_refl
                        | Fᵏ' => match v in val k0 return k0 = Fᵏ -> elem_dec Fᵏ with
                                 | vFLam t0    => fun _ => ed_red (rFApp t0 t)
                                 | vFVar n     => fun _ => ed_dec _ t (ap_l Fᵏ' (vEaVar n))
                                 | vFApp v1 v2 => fun _ => ed_dec _ t (ap_l Fᵏ' (vEaApp v1 v2))
                                 | _ => _
                                 end eq_refl
                          end
      | ap_l k0 v0  => fun v => match k0 as k0 return elem_dec k0 with
                                | Eᵏ' => ed_val (vEApp v0 v)
                                | Fᵏ' => ed_val (vFApp v0 v)
                                end

      | esub_c k0 d => fun v => match v in val k1 return k1 = Dᵏ -> elem_dec k0 with
                                | vDLam t0    => fun _ => ed_red (rSubLam _ t0 d)
                                | vDVar n     => fun _ => ed_red (rSubVar _ n  d)
                                | vDApp t1 t2 => fun _ => ed_red (rSubApp _ t1 t2 d)
                                | _ => _
                                end eq_refl

      end v.

  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)
  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).

  Proof.
    destruct k, t; simpl;
    auto.
  Qed.


  (* The two pairs (term, context) before and after decomposition represent the same term. *)
  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).

  Proof.
    intros ? ? ec v.
    destruct ec; dependent destruction v; destruct_all EF_kind;
    simpl;
    try solve [ auto ].
  Qed.


  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.

  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)
  Definition search_order
      (k : ckind) t (ec ec0 : elem_context_in k) : Prop :=

      let (_, ec)  := ec  in
      let (_, ec0) := ec0 in

      match ec, ec0 with
                    | ap_l _ _, ap_r _ _ => immediate_ec ec t /\ immediate_ec ec0 t
                    | _, _               => False
                    end.

  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).
  Notation "[ k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
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

  (* The search order is well-founded. *)
  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof.
    intros k t [? ec];
    destruct t, ec;
    repeat
    (let k0 := fresh k  in
     let ec := fresh ec in
     let H  := fresh H  in
     constructor;
     intros [k0 ec] H;
     dependent destruction ec;
     destruct_all EF_kind; try discriminate;
     dep_subst;
     try (inversion H; dep_subst; clear H)).
  Qed.


  (* The search order is transitive. *)
  Lemma search_order_trans :                                      forall k t ec0 ec1 ec2,
      [ k, t |~ ec0 << ec1  ->  [ k, t |~ ec1 << ec2  ->  [ k, t |~ ec0 << ec2.

  Proof.
    intros k t [? ec0] [? ec1] [? ec2] H H0.
    destruct ec0; dependent destruction ec1;
    destruct_all EF_kind; try discriminate;
    dep_subst;
    try solve [ autof ].
  Qed.


  (* All immediate prefixes are comparable in this order, that is: *)
  (* If we have two productions in the grammar of the form  k-> ec0[k'] and k-> ec1[k''] *)
  (* and the two elementary contexts are prefixes of the same term then they are comparable. *)
  Lemma search_order_comp_if :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

      immediate_ec ec0 t -> immediate_ec ec1 t ->
          [ k, t |~ ec0 << ec1 \/ [ k, t |~ ec1 << ec0 \/ ( k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.
    destruct ec0; dependent destruction ec1;
    destruct_all esub; destruct_all esubstitute;
    destruct_all EF_kind; try discriminate;
    subst;
    inversion H5; subst;

    try solve
    [ compute; eautof 7
    | do 2 right;
      split;
    [ auto
    | match goal with H : (valCa_to_term _) = (valCa_to_term _) |- _ =>
      apply valCa_to_term_injective in H;
      subst;
      auto
      end
    ] ].
  Qed.


  (* Only immediate prefixes are comparable in this order. *)
  Lemma search_order_comp_fi :                                          forall t k k' k''
                      (ec0 : elem_context_kinded k k') (ec1 : elem_context_kinded k k''),

       [ k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t.

  Proof with auto.
    intros t k k'' k''' ec0 ec1 H.
    destruct ec0; dependent destruction ec1;
    destruct_all esub; destruct_all esubstitute;
    destruct_all EF_kind; try discriminate;
    subst;
    inversion H;
    solve [auto].
  Qed.

  (* The down-arrow function always chooses the maximal element. *)
  Lemma dec_term_term_top :                                             forall k k' t t',

       forall (ec : elem_context_kinded k k'),
           dec_term t k = ed_dec _ t' ec -> so_maximal ec t.

  Proof.
    intros ? ? t t' ec H [? ec'] H0.
    destruct t, ec; dependent destruction ec';
    destruct_all EF_kind; try discriminate;
    inversion H; inversion H0.
  Qed.


  (* If the up-arrow function returns a redex, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from the minimal element. *)
  Lemma dec_context_red_bot :                   forall k k' (v : value k') (r : redex k),

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].

  Proof.
    intros ? ? v r ec H [? ec'].
    destruct ec; dependent destruction ec'; dependent destruction v;
    destruct_all EF_kind; try discriminate;
    subst;
    try solve
    [ autof
    | inversion H;
      intro G;
      unfold search_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0;
      autof ].
  Qed.


  (* The same for the case of a value: *)
  (* If the up-arrow function returns a value, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from the minimal element. *)
  Lemma dec_context_val_bot :                               forall k k' v {v' : value k},

      forall (ec : elem_context_kinded k k'),
          dec_context ec v = ed_val v' -> so_minimal ec ec:[v].

  Proof.
    intros ? ? v v' ec H [? ec'].
    destruct ec; dependent destruction ec'; dependent destruction v;
    destruct_all EF_kind; try discriminate;
    subst;
    solve [ autof ].
  Qed.


  (* If the up-arrow function returns that we should continue searching, *)
  (* it chooses the next (according to the order) element, that is, the predecessor. *)
  Lemma dec_context_term_next :                                      forall k0 k1 k2 v t,

      forall (ec0 : elem_context_kinded k0 k1) (ec1 : elem_context_kinded k0 k2),
          dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0; dependent destruction ec1; dependent destruction v;
    destruct_all EF_kind; try discriminate;
    subst;
    try solve
    [ autof

    | inversion H; subst;
      split;
      [ constructor;
        compute; eauto
      | intros [? ec''] H0 H1;
        dependent_destruction2 ec'';
        destruct_all EF_kind; try discriminate;
        subst;
        solve [ autof ]
      ] ].
  Qed.


  (* If there are two overlapping elementary contexts in the same term, then the greater *)
  (* of them contains no redices (it contains only values). *)
  Lemma elem_context_det :            forall k0 k1 k2 t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

          t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].

  Proof.
    intros ? ? ? t ec0 ec1 H0.

    destruct ec0; dependent destruction ec1;
    destruct_all EF_kind; try discriminate;
    subst;
    autof.
    unfold search_order in H0; destruct H0 as (H, G);
    destruct (valCa_is_valECa v) as (v0, H0).
    - exists v0.
      simpl; rewrite <- H0.
      inversion H as (t1, H1); inversion G as (t2, G1).
      compute in *; congruence.
    - destruct v as [x | v0 v1];
      [ exists (vFVar x) | exists (vFApp v0 v1) ];
      apply search_order_comp_fi in H0;
      destruct H0 as [(?, H1) (?, H2)];
      compute in *; congruence.
  Qed.

End Lam_SES_NO_Strategy.





(* Contexts from the Johan Munk's paper:
   "Basic Research in Computer Science
   A Study of Syntactic and Semantic Artifacts
   and its Application to
   Lambda Definability, Strong
   Normalization, and Weak Normalization
   in the Presence of State" *)

(* In this paper the authors construct by hand an abstract machine for
lambda calculus with normal order and simple explicit
substitutions. They use a different definition of evaluation contexts,
in particular they use inside-out grammars of contexts (while we use
outside-in grammars). Below we show that there is a direct
correspondence between their and our contexts. *)

Module Lam_SES_NO_AlterContexts.

  Import Lam_SES_NO_PreRefSem.

  Inductive ckind_IO := Aio | Cio | Dio.

(* Here is the definition of their contexts *)

  Inductive context_IO : ckind_IO -> Type :=
  | hole_io   : context_IO Aio
  | ap_l_io   : context_IO Cio -> valCa -> context_IO Aio
  | lam_c_io  : context_IO Aio -> context_IO Aio

  | a_is_c_io : context_IO Aio -> context_IO Cio
  | ap_r_io   : context_IO Cio -> term -> context_IO Cio

  | c_is_d_io : context_IO Cio -> context_IO Dio
  | esub_c_io : context_IO Dio -> esub -> context_IO Dio.

  Definition a_is_d_io c := c_is_d_io (a_is_c_io c).


  (* Here a mapping from our to their contexts *)
  Definition context_to_IO {k1 k2} (c : context k1 k2) :
               match k2 with
               | Eᵏ => context_IO Aio | Fᵏ => context_IO Cio
               | Dᵏ => context_IO Dio
               end.

    induction c as  [ | k2 k3 ec c IHc].

    (* c = [.] *)
    - destruct k1.
      + exact hole_io.
      + exact (a_is_c_io hole_io).
      + exact (a_is_d_io hole_io).

    (* c = (ec=:c') *)
    - set (e:=ec).
      destruct ec; destruct_all EF_kind;
      simpl in IHc;
      match goal with
      | e := lam_c                             |- _ => exact (lam_c_io IHc)
      | e := ap_r _ ?t, IHc : context_IO Aio   |- _ => exact (ap_r_io (a_is_c_io IHc) t)
      | e := ap_r _ ?t, IHc : context_IO Cio   |- _ => exact (ap_r_io IHc t)
      | e := ap_l _ ?v, IHc : context_IO Aio   |- _ => exact (ap_l_io (a_is_c_io IHc) v)
      | e := ap_l _ ?v, IHc : context_IO Cio   |- _ => exact (ap_l_io IHc v)
      | e := esub_c ?k ?d |- _ =>
           destruct k;
           match goal with
           | IHc : context_IO Aio |- _ => exact (esub_c_io (a_is_d_io IHc) d)
           | IHc : context_IO Cio |- _ => exact (esub_c_io (c_is_d_io IHc) d)
           | IHc : context_IO Dio |- _ => exact (esub_c_io IHc d)
           end
      end.
  Defined.

  (* Here is a mapping from their into our contexts *)
  Definition context_from_IO {k} (c : context_IO k) :
               match k with
               | Aio => context Eᵏ Eᵏ | Cio => context Eᵏ Eᵏ + context Eᵏ Fᵏ
               | Dio => context Eᵏ Eᵏ + context Eᵏ Fᵏ + context Eᵏ Dᵏ
               end.

    set (c0:=c).
    induction c as [ | ? IHc ? | ? IHc | ? IHc | ? IHc ? | ? IHc | ? IHc ?]; simpl in *;
    try match goal with
    | c0 := hole_io        |- _ => exact [.]
    | c0 := ap_l_io _ ?v   |- _ => destruct IHc as [IHc | IHc];
                                   [ exact (ap_l Eᵏ' v=:IHc)
                                   | exact (ap_l Fᵏ' v=:IHc)]
    | c0 := lam_c_io _     |- _ => exact (lam_c=:IHc)
    | c0 := a_is_c_io _    |- _ => exact (inl IHc)
    | c0 := ap_r_io _ ?t   |- _ => destruct IHc as [IHc | IHc];
                                   [ exact (inr (ap_r Eᵏ' t=:IHc))
                                   | exact (inr (ap_r Fᵏ' t=:IHc)) ]
    | c0 := c_is_d_io _    |- _ => exact (inl IHc)
    | c0 := esub_c_io _ ?d |- _ => destruct IHc as [[IHc | IHc] | IHc];
                                   exact (inr (esub_c _ d=:IHc))
    end.
  Defined.


  (* the composition of the two mappings is the identity on their contexts *)
  Lemma to_from_IO_is_id :
            forall k (c : context_IO k),
                match k as k return context_IO k -> Prop with
                | Cio => fun c =>
                    c = match context_from_IO c with
                        | inl c => a_is_c_io (context_to_IO c)
                        | inr c => context_to_IO c
                        end
                | Aio => fun c => c = context_to_IO (context_from_IO c)
                | Dio => fun c =>
                    c = match context_from_IO c with
                        | inl (inl c) => a_is_d_io (context_to_IO c)
                        | inl (inr c) => c_is_d_io (context_to_IO c)
                        | inr c => context_to_IO c
                        end
                end c.
  Proof.
    induction c;
        simpl;
        repeat match goal with
        | _ : context [match ?s with inl _ => _ | inr _ => _ end] |- _ => destruct s
        end;
        try subst;
    solve
    [ simpl; f_equal; auto ].
  Qed.

(* the other composition of the two mappings is the identity on our contexts *)
  Lemma from_to_IO_is_id :
            forall k (c : context Eᵏ k),
                match k as k return context Eᵏ k -> Prop with
                | Eᵏ => fun c =>     c = context_from_IO (context_to_IO c)
                | Fᵏ => fun c => inr c = context_from_IO (context_to_IO c)
                | Dᵏ => fun c => inr c = context_from_IO (context_to_IO c)
                end c.
  Proof.
    induction c as [ | k1 k2 ec ? IHc].
    - simpl; auto.
    - destruct ec; destruct_all EF_kind;
      try match goal with |- inr (esub_c ?k ?e =: ?c) = _
          => destruct k end;
      simpl;
      try rewrite <- IHc;
      try solve [congruence | auto].
  Qed.


  (* The plug function on their contexts *)
  Fixpoint plug_IO t {k} (c : context_IO k) :=
      match c with
      | hole_io       => t
      | ap_l_io c' v  => plug_IO (App (v : term) t) c'
      | lam_c_io c'   => plug_IO (Lam t) c'
      | a_is_c_io c'  => plug_IO t c'
      | ap_r_io c' t' => plug_IO (App t t') c'
      | c_is_d_io c'  => plug_IO t c'
      | esub_c_io c' (n, st_sub t')  => plug_IO (Sub t n t') c'
      | esub_c_io c' (n, st_shift m) => plug_IO (Shift t n m) c'
      end.

  (* plugging a term into our context is the same as (their) plugging this term into the translation of the context to their contexts *)
  Lemma plug_compatible :
          forall {k1 k2} (c : context k1 k2) t,
              match k2 as k2 return context k1 k2 -> Prop with
              | Eᵏ | Fᵏ | Dᵏ => fun c => c[t] = plug_IO t (context_to_IO c)
              end c.
  Proof.
    induction c.
    - destruct k1; auto.
    - destruct ec;
      destruct_all esub; destruct_all esubstitute;
      destruct_all EF_kind; destruct_all ckind;
      try solve [simpl in *; auto].
  Qed.


  (* plugging a term into their context is the same as plugging this term into the translation of this context to our contexts *)
  Lemma plug_compatible2 :
          forall {k} (c : context_IO k) (t : term),
              plug_IO t c =
              match k as k return context_IO k -> term with
              | Aio => fun c => (context_from_IO c)[t]
              | Cio => fun c => match context_from_IO c with
                                | inl c | inr c => c[t] end
              | Dio => fun c => match context_from_IO c with
                                | inl (inl c) | inl (inr c) | inr c => c[t] end
              end c.
  Proof.
    intros k c t.
    symmetry.
    destruct k;
        first
        [ rewrite (to_from_IO_is_id Aio) at 2
        | rewrite (to_from_IO_is_id Cio) at 2
        | rewrite (to_from_IO_is_id Dio) at 2 ];
        repeat match goal with
        | |- context [match ?s with inl _ => _ | inr _ => _ end] => destruct s
        end;
    solve
    [ apply @plug_compatible with (k2 := Eᵏ)
    | apply @plug_compatible with (k2 := Fᵏ)
    | apply @plug_compatible with (k2 := Dᵏ) ].
  Qed.

End Lam_SES_NO_AlterContexts.


(* The refocusable semantics is composed from the reduction semantics and the reduction strategy *)
Module Lam_SES_NO_RefSem := RedRefSem Lam_SES_NO_PreRefSem Lam_SES_NO_Strategy.




Require Import refocusing_machine.

(* And the abstract machine is generated from this semantics *)
Module Lam_SES_NO_EAM := RefEvalApplyMachine Lam_SES_NO_RefSem.
