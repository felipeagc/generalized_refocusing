(* Lambda calculus with call by name reduction strategy *)

Require Import Program
               Util
               refocusing_semantics.

(* Here we define the reduction semantics. *)
(* The module type PRE_REF_SEM is defined in the file *)
(*     refocusing/refocusing_semantics.v *)
(* It inherits part of the signature from RED_SEM defined in *)
(*     reduction_semantics/reduction_semantics.v *)

Module Lam_cbn_PreRefSem <: PRE_REF_SEM.

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

  Coercion value_to_term : value >-> term.
  
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
  Coercion redex_to_term : redex >-> term.

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

  Inductive eck : ckind -> ckind -> Set := 
  | ap_r  : term -> eck Cᵏ Cᵏ. (* Cᵏ -> Cᵏ t *)
  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  Cᵏ.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

  (* Again a technicality: the plug function is injective. *)
  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ? ? ec t0 t1 H.
    destruct ec;
    solve
    [ inversion H; trivial ].
  Qed.


  (* A context is a stack of elementary contexts. *)
  (* The first parameter is the nonterminal generating the whole *)
  (* context, the second is the kind of the hole. *)
  (* We use inside-out representation of contexts, so the topmost symbol on the stack *)
  (* is the elementary context that is closest to the hole. *)
  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons :                                                                forall {k2 k3}
            (ec : elem_context_kinded k2 k3), context k1 k2 -> context k1 k3.
  Arguments empty {k1}. Arguments ccons {k1 k2 k3} _ _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).


  (* Contexts may be composed (i.e., nested). *)
  (* The first parameter is the internal context, the second is external. *) 
  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).



  (* The function for plugging a term into an arbitrary context *)
  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).

  (* Here we define what it means that an elementary context ec is a prefix of *)
  (* a term t. *) 
  Definition immediate_ec {k1 k2} (ec : elem_context_kinded k1 k2) t :=
      exists t', ec:[t'] = t.

  (* The same for immediate subterms *)
  Definition immediate_subterm t0 t := exists k1 k2 (ec : elem_context_kinded k1 k2),
      t = ec:[t0].

  (* Next technicality: immediate_subterm has to be proved to be well-founded. *)
  (* Here we use a macro that does this for us. *)
  Lemma wf_immediate_subterm: well_founded immediate_subterm.
  Proof.    REF_LANG_Help.prove_st_wf.
  Qed.

  
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

  (* Decomposition of a term is a pair consisting of a reduction context and *)
  (* a potential redex. Values have no decomposition; we just report that *)
  (* the term is a value. *)
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

  (* Syntactic sugar: term t decomposes to decomposition d *)
  Definition dec (t : term) k (d : decomp k) : Prop := 
    t = d.

  
  (* Subterm order is the transitive closure of the immediate_subterm relation. *)
  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).

  (* Subterm order is a well founded relation *)
  Definition wf_subterm_order : well_founded subterm_order
    := wf_clos_trans_l _ _ wf_immediate_subterm.

  (* Here we define the reduction relation. Term t1 reduces to t2 wrt. k-strategy *)
  (* if t1 decomposes to r : redex k' and c : context k k', and r rewrites (wrt. *)
  (* k'-contraction) to t and t2 = c[t]. *)
  Definition reduce k t1 t2 := 
    exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
                                                      contract r = Some t /\ t2 = c[t].

  (* Reduction relation gives an instance of a rewriting system *) 
  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
    { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
    { transition := reduce init_ckind }.

  (* Again some technicalities required by the module *)
  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
    { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
    }.

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

  (* This ends the definition of the reduction sematnics *)
End Lam_cbn_PreRefSem.


(* Although a reduction semantics implicitly contains reduction strategy, our *)
(* implementation requires an explicit (lower-level) definition of this strategy. *)
(* So now we define such a reduction strategy. *)

(* The module type REF_STRATEGY is defined in the file *)
(*     refocusing/refocusing_semantics.v. *)
Module Lam_cbn_Strategy <: REF_STRATEGY Lam_cbn_PreRefSem.

  Import Lam_cbn_PreRefSem.

  (* Here we define the two functions: up arrow and down arrow. *)
  (* We start by defining the type returned by these functions. *)
  (* They return that the input term is either a redex (ed_red) *)
  (* or a value (ed_val) or that we have to continue searching  *)
  (* inside a subterm (ed_dec) *)  
  Inductive elem_dec k : Set :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.


  
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

  Lemma dec_term_correct : 
    forall (t : term) k, match dec_term t k with
                         | ed_red r      => t = r
                         | ed_val v      => t = v
                         | ed_dec _ t' ec => t = ec:[t']
                         end.
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
  Lemma dec_context_correct :         forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r        => ec:[v] = r
      | ed_val v'       => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.

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

  Inductive elem_context_in k : Set :=
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


(* List of numbered configurations while executing the machine on configuration c
   for n steps and starting the numbering from i  *)
Fixpoint list_configs c n i := 
 match n with 
 | 0 => nil
 | S n' =>  match c with 
            | None => nil
            | Some c' => cons (i,c')  (list_configs (n_steps c' 1) n' (S i))
            end
 end.


(* List of numbered configurations while executing the machine for n steps on term t *)
Fixpoint list_configurations t n := list_configs (Some (load t)) n 1.

Eval compute in list_configurations  t 8 .


(* and the complete machine *)
Print Lam_cbn_EAM.

