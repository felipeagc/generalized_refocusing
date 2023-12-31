(* Lambda calculus with call by name reduction strategy *)

Require Import Program
               Util
               refocusing_semantics.

(* Here we define the reduction semantics. *)
(* The module type PRE_RED_SEM is defined in the file *)
(*     reduction_semantics/reduction_semantics.v *)
(* It is a RED_SEM without totality of decompose *)

Module Lam_cbn_PreRefSem <: PRE_RED_SEM.

  (* The first parameter required by RED_SEM is the set of terms. *)
  (* To define it, we first have to define variables and prove *)
  (* that their equality is decidable. *)

  (* We define variables as numbered identifiers. *)
  Inductive id :=
  | Id : nat -> id.


  Definition var := id.

  Theorem eq_var : forall x y : var, {x = y} + {x <> y}.
  Proof.
    intros x.
    destruct x as [n]. induction n.
    - intros y.
      destruct y as [m]. destruct m.
      + left. reflexivity.
      + right. intros contra. inversion contra.
    - intros y. destruct y as [m].
      destruct m as [|m'].
      + right. intros contra. inversion contra.
      + destruct IHn with (y := Id m') as [eq | neq].
        left. apply f_equal.  inversion eq. reflexivity.
        right. intros Heq. inversion Heq as [Heq']. apply neq. rewrite Heq'. reflexivity.
  Defined.


  (* Here we define the language of interest: lambda calculus. *)
  (* In Coq it is not possible to define parameter of a module *)
  (* as an inductive type, therefore we first define inductively *)
  (* expressions and only then we define terms as expressions. *)
  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr.
  Definition term := expr.
  Hint Unfold term.


  (* The main ingredient of a reduction semantics is a grammar of contexts.  *)
  (* We start with nonterminal symbols, which are called here "context kinds". *)

  (* In call by name one context kind Cᵏ is enough. *)

  Inductive ck := Cᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.

  (* Now we define (for each context kind) the set of values. *)
  (* In call by name they are simply lambda abstractions. *)
  (* For technical reasons we have to use fresh constructors; later we will *)
  (* use a coercion to identify values with the corresponding lambda terms. *)

  Inductive val : ckind -> Type :=
  | vLam : var -> term  -> val Cᵏ.

  Definition value := val.
  Hint Unfold value.

  (* The coercion is a simple function that changes occurrences of vLam *)
  (* constructors to Lam. *)
  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vLam x t => Lam x t
      end.

  (* Here we define the set of potential redices. *)
  (* They are either redices (lambda abstractions applied to terms) *)
  (* or variables, which applied to other terms give stuck terms.  *)

  Inductive red : ckind -> Type :=
  | rApp : var -> term -> term -> red Cᵏ
  | rStuck: var  -> red Cᵏ.
  Definition redex := red.
  Hint Unfold redex.

  (* Again we use a coercion to identify redices with the corresponding lambda terms. *)
  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp x t t'   => App (Lam x t) t'
      | rStuck x    =>  Var x
      end.


  (* Here comes the actual definition of the grammar of contexts. *)
  (* Each constructor of eck represents a (nontrivial) production. *)
  (* We have just one nontrivial production here:  Cᵏ -> Cᵏ t  *)
  (* which says that a context is another context applied to a term. *)
  (* Non-context nonterminals/variables (like t) are represented as parameters of *)
  (* the constructors of the appropriate types (values of these types should *)
  (* form the languages generated from these nonterminals). *)
  (* There is also a trivial production  Cᵏ -> [] which is omitted here. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *)


  Inductive eck : ckind -> ckind -> Type :=
  | ap_r  : term -> eck Cᵏ Cᵏ. (* Cᵏ -> Cᵏ t *)
  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.


  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  Cᵏ.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      end.

  (* Here we define substitutions, which is necessary to define contraction. *)
  (* Be careful: the definition works only for closed terms s and  *)
  (* we do not check if a substitution is capture-avoiding. *)

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

  (* Example: to see how a substitution works, uncomment the lines below *)
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 1). (* [x:= \y.y] x *)*)
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 2). (* [x:= \y.y] y *)*)


  (* Now we are ready to define the contraction. In our case this is simply beta *)
  (* reduction. *)
  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp x t0 t1 => Some ([x := t1] t0)
      | rStuck x  => None
      end.

  (* Having this we include some basic notions *)
  Include RED_SEM_BASE_Notions.

  (* Some technicalities: it should be obvious that the two coercions are injective *)
  (* This again is a required axiom in the signature of RED_SEM module *)
  Lemma value_to_term_injective :
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    destruct v. intros.
    dependent destruction v'.   inversion H. reflexivity.
  Qed.


  Lemma redex_to_term_injective :
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    intros k r r' H.
    destruct r ; dependent destruction r';
    inversion H; subst;
    f_equal;
    inversion H.
  Qed.

  (* Again a technicality: the plug function is injective. *)
  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    solve
    [ inversion H; trivial ].
  Qed.

  (* Next technicality: immediate_subterm has to be proved to be well-founded. *)
  (* Here we use a macro that does this for us. *)
  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof.    REF_LANG_Help.prove_st_wf.
  Qed.

  (* Subterm order is a well founded relation *)
  Definition wf_subterm_order : well_founded subterm_order
    := wf_clos_trans_l _ _ wf_immediate_subterm.


  (* Decomposition of a value cannot give a potential redex, it must give a value. *)
  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                             exists (v' : value k2), t = v'.
  Proof.
    intros ? ? ec t v H.
    destruct ec.   dependent destruction v. inversion H.
  Qed.

  (* A value is not a redex. *)
  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.
    destruct r; destruct v; intro H; inversion H.
  Qed.

  (* There are no other potential redices inside a potential redex; *)
  (* there can be only values. *)
  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof.
    intros ? ? r ec t H.
    destruct ec; dependent destruction r;
    subst; inversion H.
    exists (vLam v t);reflexivity.
  Qed.


  (* This ends the definition of the reduction semantics *)
End Lam_cbn_PreRefSem.


(* Although a reduction semantics implicitly contains reduction strategy, our *)
(* implementation requires an explicit (lower-level) definition of this strategy. *)
(* So now we define such a reduction strategy. *)

(* The module type REF_STRATEGY is defined in the file *)
(*     refocusing/refocusing_semantics.v. *)
Module Lam_cbn_Strategy <: REF_STRATEGY Lam_cbn_PreRefSem.

  Import Lam_cbn_PreRefSem.
  Include RED_STRATEGY_STEP_Notions Lam_cbn_PreRefSem.


  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)
  (* The function says what to do when we try to evaluate a term. The *)
  (* first rule says that when we evaluate an application, we start by *)
  (* evaluating the left argument (the calling function). The second rule *)
  (* says that when we evaluate a variable, we end up in a stuck term *)
  (* (this should never happen if we start with a closed term). The third *)
  (* rule says that when we evaluate a lambda abstraction, we already *)
  (* have a value.  *)
  Definition dec_term t k : elem_dec k :=
    match k with Cᵏ =>
                 match t with
                 | App t1 t2 => ed_dec  Cᵏ t1 (ap_r t2)
                 | Var x     => ed_red (rStuck x)
                 | Lam x t1  => ed_val (vLam x t1)
                 end
    end.



  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)

  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).
  Proof.
    destruct k,t ; simpl; auto.
  Qed.




  (* Here is the up-arrow function. *)
  (* It is used to decompose a context. *)
  (* This function says what to do when we finish evaluation of a subterm. *)
  (* In call by name it means that we find a lambda abstraction and we are ready *)
  (* to contract (beta-reduce). *)
  Definition dec_context  {k k': ckind} (ec: elem_context_kinded k k') (v: value k')
                                                                          : elem_dec k :=
    match ec with
    | ap_r t   =>  match v with
                   | vLam x t' => ed_red  (rApp x t' t)
                   end
    end.

  (* The two pairs (term, context) before and after decomposition represent *)
  (* the same term. *)
  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).

  Proof.
    intros ? ? ec v.
    destruct ec; dependent destruction v;
      simpl;
      try solve [ auto ].
  Qed.


  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)

  (* The construction is quite technical. *)
  (* In the case of call-by-name strategy it is not really illustrative, because *)
  (* even if the constructed order is trivial, we still have to prove all *)
  (* the properties required in the signature of the module. *)

  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  (* In the case of call-by-name the order is trivial. *)
  (* We have only one production in the grammar and there are no overlapping *)
  (* elementary contexts. There is simply nothing to compare. *)
  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop :=
    False.


  (* But we still have to go through all of the following. *)
  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                   (at level 70, ec1, ec2 at level 50, no associativity).

  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2)
                                     (no associativity, at level 70, ec1, t at level 69).

  (* The search order is well-founded. *)
  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof.
    intros ? ? ?.
    constructor.
    intros ? H.
    inversion H.
  Qed.


  (* The search order is transitive. *)
  Lemma search_order_trans :                                      forall k t ec0 ec1 ec2,
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 ->
      k,t |~ ec0 << ec2.

  Proof.
    intros k t ec0 ec1 ec2 H H0.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.


  (* All immediate prefixes are comparable in this order, that is: *)
  (* If we have two productions in the grammar of the form  k-> ec0[k'] and *)
  (* k-> ec1[k''] and the two elementary contexts are prefixes of the same term, *)
  (* then they are comparable. *)
  Lemma search_order_comp_if :         forall t k k' k'' (ec0 : elem_context_kinded k k')
                                                       (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    subst.
    inversion H5; subst.

    solve
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


  (* Only immediate prefixes are comparable in this order. *)
  Lemma search_order_comp_fi :
      forall t k k' k'' (ec0 : elem_context_kinded k k')
                        (ec1 : elem_context_kinded k k''),
          k, t |~ ec0 << ec1 ->
              immediate_ec ec0 t /\ immediate_ec ec1 t.


  Proof with auto.
    intros t k k'' k''' ec0 ec1 H.
    inversion H.
  Qed.


  (* Order-related definitions *)

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


  (* The down-arrow function always chooses the maximal element. *)

  Lemma dec_term_term_top : forall {k k'} t t' (ec : elem_context_kinded k k'),
          dec_term t k = ed_dec _ t' ec -> so_maximal ec t.
  Proof.
    intros t k t' ec H ec' H0.
    destruct k, t, ec'; inversion H;  subst; inversion H0.
    intro HHH. inversion HHH.
  Qed.

  (* If the up-arrow function returns a redex, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from *)
  (* the minimal element. *)
  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof.
    intros k ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    solve
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
  (* There are no further redices, i.e., we have just returned from *)
  (* the minimal element. *)
  Lemma dec_context_val_bot : forall {k k'} (v : value k') {v' : value k}
      (ec : elem_context_kinded k k'),
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
  Proof.
    intros k ec v v' H ec'.
    destruct k, ec, ec'; dependent destruction v;
    solve [ autof ].
  Qed.


  (* If the up-arrow function returns that we should continue searching, *)
  (* it chooses the next (according to the order) element, that is, the predecessor. *)
  Lemma dec_context_term_next :                        forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0; dependent destruction ec1;  dependent destruction v;
    try discriminate.
  Qed.


  (* If there are two overlapping elementary contexts in the same term, then *)
  (* the greater of them contains no redices (it contains only values). *)
  Lemma elem_context_det :          forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),

      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].

  Proof.
    intros ? ? ? t ec0 ec1 H0.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    subst;
    autof.
  Qed.

End Lam_cbn_Strategy.


(* The refocusable semantics is composed from the reduction semantics and *)
(* the reduction strategy *)
Module Lam_cbn_RefSem := RedRefSem Lam_cbn_PreRefSem Lam_cbn_Strategy.


(* And the abstract machine is generated from this semantics *)
Require Import refocusing_machine.
Module Lam_cbn_EAM := RefEvalApplyMachine Lam_cbn_RefSem.


(* An example computation of the generated machine *)
Import Lam_cbn_PreRefSem.
Import Lam_cbn_EAM.
Require Import abstract_machine_facts.
Module Lam_cbn_sim := DetAbstractMachine_Sim Lam_cbn_EAM.
Import Lam_cbn_sim.

Definition x  := Id 1.
Definition xx := (Lam x (App (Var x) (Var x))).
Definition id := (Lam x (Var x)).
Definition t  := (App xx id).

Eval compute in list_configurations t 8 .


(* and the complete machine *)
Print Lam_cbn_EAM.

