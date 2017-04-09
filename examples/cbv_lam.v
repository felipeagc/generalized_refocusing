(* Lambda calculus with left-to-right call-by-value  reduction strategy *)

Require Import Program
               Util
               refocusing_semantics.


(* Here we define the reduction semantics. *)
(* The module type PRE_REF_SEM is defined in  the file refocusing/refocusing_semantics.v *)
(* It inherits part of the signature from RED_SEM defined in reduction_semantics/reduction_semantics.v *)

Module Lam_cbv_PreRefSem <: PRE_REF_SEM.

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

  (* In call by value one context kind Cᵏ is enough. *)

  Inductive ck := Cᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.

  (* Now we define (for each context kind) the set of values. *)
  (* In left-to-right call-by-value they are simply lambda abstractions.  *)
  (* For technical reasons we have to use fresh constructors; later we will *)
  (* use a coercion to identify values with the corresponding lambda terms. *)  

  Inductive val : ckind -> Type :=
  | vLam : var -> term -> val Cᵏ.

  Definition value := val.
  Hint Unfold value.

  (* The coercion is a simple function that changes occurrences of vLam constructors to Lam. *)
  Fixpoint value_to_term {k} (v : value k) : term :=
    match v with
      | vLam x t => Lam x t
    end.

  Coercion value_to_term : value >-> term.
  
  (* Here we define the set of potential redices. *)
  (* They are either redices (lambda abstractions applied to terms) *)
  (* or variables, which applied to other terms give stuck terms.  *)

  Inductive red : ckind -> Type :=
  | rApp : var -> term -> value Cᵏ -> red Cᵏ
  | rStuck: var  -> red Cᵏ. 
  Definition redex := red.
  Hint Unfold redex.

  (* Again we use a coercion to identify redices with the corresponding lambda terms. *)  
  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp x t v   => App (Lam x t) (value_to_term v)
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
    dependent destruction  r ; dependent destruction r';
    inversion H;   try apply (value_to_term_injective v0 v2)  in H3;  subst; reflexivity. 
  Qed.

  
  (* Here comes the actual definition of the grammar of contexts. *)
  (* We have two nontrivial productions:  Cᵏ -> Cᵏ t  and Cᵏ -> v Cᵏ *)
  (* which says that a context is another context applied to a term *)
  (* or a value applied to another context. *)
  (* There is also a trivial production  Cᵏ -> [] which is omitted here. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *) 
  Inductive eck : ckind -> ckind -> Set := 
  | ap_r  : term -> eck Cᵏ Cᵏ (* Cᵏ -> Cᵏ t *)
  | ap_l  : value Cᵏ -> eck Cᵏ Cᵏ.  (* Cᵏ +> v Cᵏ *) 

  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  Cᵏ.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      | ap_l  v => App (v: term) t
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
  (* We use the inside-out representation of contexts, so the topmost symbol on the stack *)
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

  (* Here we define what it means that an elementary context ec is a prefix of a term t. *) 
  Definition immediate_ec {k1 k2} (ec : elem_context_kinded k1 k2) t :=
      exists t', ec:[t'] = t.

  (* The same for immediate subterms *)
  Definition immediate_subterm t0 t := exists k1 k2 (ec : elem_context_kinded k1 k2),
      t = ec:[t0].

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
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 1). (* [x:= \y.y] x *) *)
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 2). (* [x:= \y.y] y *) *)


  (* Now we are ready to define the contraction. In our case this is simply beta reduction. *)
  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp x t0 t1 => Some ([x := t1] t0)
      | rStuck x  => None 
      end.

  (* Decomposition of a term is a pair consisting of a reduction context and a potential redex. *)
  (* Values have no decomposition; we just report that the term is a value. *)
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
  (* if t1 decomposes to c[r] and r rewrites (wrt. k-contraction) to t and t2=c[t]. *)
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
    destruct ec;   dependent destruction v; inversion H. 
  Qed.

  (* A value is not a redex. *)
  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.
    destruct r; destruct v; intro H; inversion H. 
  Qed.

  (* There are no other (potential) redices inside a redex; there can be only values. *)
  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof.
    intros ? ? r ec t H0.

    destruct r.
    *   dependent destruction v0 ;  inversion H0;  dependent destruction ec;
        eexists (vLam _ _); inversion H1; reflexivity.
    *   dependent destruction ec;  inversion H0.    
  Qed.

  (* This ends the definition of the reduction sematnics *)
End Lam_cbv_PreRefSem.


(* Although a reduction semantics implicitly contains reduction strategy, our implementation 
   requires an explicit definition of this strategy. So now we define the reduction strategy.  *)


(* The module type REF_STRATEGY is defined in the file refocusing/refocusing_semantics.v. *)
Module Lam_cbv_Strategy <: REF_STRATEGY Lam_cbv_PreRefSem.

  Import Lam_cbv_PreRefSem.

  (* Here we define the two functions: up arrow and down arrow. *)
  (* We start by defining the type returned by these functions.  *)
  (* They return that the input term is either a redex (in_red) *)
  (* or a value (in_val) or that we have to continue searching  *)
  (* inside a subterm (in_term) *)  
  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : forall k', term -> elem_context_kinded k k' -> interm_dec k
  | in_val  : value k -> interm_dec k.
  Arguments in_red {k} _.       Arguments in_val {k} _.
  Arguments in_term {k} k' _ _.


  
  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)  
  (* The function says what to do when we try to evaluate a term.  The
  first rule says that when we evaluate an application, we start by
  evaluating the left argument (the calling function). The second rule
  says that when we evaluate a variable, we end up in a stuck term
  (this should never happen if we start with a closed term). The third
  rule says that when we evaluate a lambda abstraction, we already
  have a value.  *)
  Definition dec_term t k : interm_dec k :=
    match k with Cᵏ => 
                 match t with
                 | App t1 t2 => in_term  Cᵏ t1 (ap_r t2)
                 | Var x     => in_red (rStuck x) 
                 | Lam x t1  => in_val (vLam x t1)
                 end
    end.



  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)

  Lemma dec_term_correct : 
    forall (t : term) k, match dec_term t k with
                         | in_red r      => t = r
                         | in_val v      => t = v
                         | in_term _ t' ec => t = ec:[t']
                         end.
  Proof.
    destruct k,t ; simpl; auto.
  Qed.



 
  (* Here is the up-arrow function. *)
  (* It is used to decompose a context.  *)

  (* Here we would like to define this function as follows.
  
  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : interm_dec k := 
    match ec with 
    | ap_r t => in_term k' t (ap_l v) 
    | ap_l v' => match v' with 
                 | vLam x t => in_red (rApp x t v) 
                 end 
  end.

  This function says what to do when we finish evaluation of a subterm.
  Here the first rule says that when we finish the evaluation of the
  calling function we start the evaluation of the argument.  The
  second rule says that when we finish the evaluation of the argument,
  we should contract (beta-reduce).

  Unfortunately, Coq is not able to infer that k and k' are the same
  as Cᵏ, and we have to do some dirty tricks.  *)

  
  Definition dec_context  {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : interm_dec k :=
    match ec in eck k k' return value k' -> interm_dec k with
    | ap_r t =>  (fun v => in_term Cᵏ t (ap_l v))
    | ap_l v' => (fun v => match v' with
                   | vLam x t => in_red  (rApp x t v)
                   end)
    end v.




  (* The two pairs (term, context) before and after decomposition represent the same term. *)
  Lemma dec_context_correct :         forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | in_red r        => ec:[v] = r
      | in_val v'       => ec:[v] = v'
      | in_term _ t ec' => ec:[v] = ec':[t]
      end.

  Proof.
    intros ? ? ec v.
    destruct ec.
    * dependent destruction v; simpl; auto.
    * dependent destruction v0; simpl; auto.
  Qed.

  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)

  (* The set of all elementary contexts generated from  nonterminal k *)
  Inductive elem_context_in k : Set :=
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

  (* The search order is well-founded. *)
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


  (* The search order is transitive. *)
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

  (* Only immediate prefixes are comparable in this order. *) 
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


  (* All immediate prefixes are comparable in this order, that is: *)
  (* If we have two productions in the grammar of the form  k-> ec0[k'] and k-> ec1[k''] *)
  (* and the two elementary contexts are prefixes of the same term then they are comparable. *)
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
    right. right. split. reflexivity.
    dependent destruction v0; dependent destruction v; inversion H5; auto.
  Qed.




  (* The down-arrow function always chooses the maximal element. *)

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
          dec_term t k = in_term _ t' ec -> so_maximal ec t.
  Proof.
    intros k k' t t' ec H ec' H0. 
    destruct t, ec; dependent destruction ec'; destruct k';
    inversion H; inversion H0.
  Qed.

  (* If the up-arrow function returns a redex, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from the minimal element. *) 
  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = in_red r -> so_minimal ec ec:[v].
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

  (* The same for the case of a value: *)
  (* If the up-arrow function returns a value, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from the minimal element. *) 
  Lemma dec_context_val_bot : forall {k k'} (v : value k') {v' : value k}
      (ec : elem_context_kinded k k'),
      dec_context ec v = in_val v' -> so_minimal ec ec:[v].
  Proof.
    intros ? ? v v' ec H [? ec'].
    destruct ec; dependent destruction ec'; dependent destruction v;
    try discriminate;
    subst;
    solve [ autof ].
  Qed.

  (* If the up-arrow function returns that we should continue searching, *)
  (* it chooses the next (according to the order) element, that is, the predecessor. *)
  Lemma dec_context_term_next :                        forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = in_term _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].
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

  (* If there are two overlapping elementary contexts in the same term, then the greater *)
  (* of them contains no redices (it contains only values). *) 
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
   exists (vLam v t). reflexivity.
 Qed.

End Lam_cbv_Strategy.


(* The refocusable semantics is composed from the reduction semantics and the reduction strategy *)
Module Lam_cbv_RefSem := RedRefSem Lam_cbv_PreRefSem Lam_cbv_Strategy.



Require Import refocusing_machine.

(* And the abstract machine is generated from this semantics *)
Module Lam_cbv_EAM := RefEvalApplyMachine Lam_cbv_RefSem.

Import Lam_cbv_PreRefSem.

Import Lam_cbv_EAM.

(* An example computation of the generated machine *)

Require Import abstract_machine_facts.
Module Lam_cbv_sim := DetAbstractMachine_Sim Lam_cbv_EAM.
Import Lam_cbv_sim.

Definition x := Id 1.
Definition xx:= (Lam x (App (Var x) (Var x))).
Definition id:= (Lam x (Var x)).
Definition t:= (App xx id).

Fixpoint list_configs c n i := 
(* List of numbered configurations while executing the machine on configuration c
   for n steps and starting the numbering from i  *)
 match n with 
 | 0 => nil
 | S n' =>  match c with 
            | None => nil
            | Some c' => cons (i,c')  (list_configs (n_steps c' 1) n' (S i))
            end
 end.

Fixpoint list_configurations t n := list_configs (Some (load t)) n 1.
(* List of numbered configurations while executing the machine for n steps on term t  *)

Eval compute in list_configurations  t 15 .

(* and the complete machine *)
Print Lam_cbv_EAM.

