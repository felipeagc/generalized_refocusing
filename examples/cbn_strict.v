(* Lambda calculus with call-by-name strategy and strictness operator *)
Set Printing Coercions.

Require Import Program
               Util
               refocusing_semantics.


(* Here we define the reduction semantics. *)
(* The module type PRE_REF_SEM is defined in  the file refocusing/refocusing_semantics.v *)
(* It inherits part of the signature from RED_SEM defined in reduction_semantics/reduction_semantics.v *)

Module Lam_cbn_strict_PreRefSem <: PRE_REF_SEM.

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


  (* Here we define the language of interest: lambda calculus with *)
  (* explicit strictness operator. *)
  (* In Coq it is not possible to define parameter of a module *)
  (* as an inductive type, therefore we first define inductively *)
  (* expressions and only then we define terms as expressions. *) 
  Inductive expr :=
  | App  : expr -> expr -> expr
  | Var  : var -> expr
  | Lam  : var -> expr -> expr
  | Bang : expr -> expr.
  Definition term := expr.
  Hint Unfold term.


  (* The main ingredient of a reduction semantics is a grammar of contexts.  *)
  (* We start with nonterminal symbols, which are called here "context kinds". *)

  (* We use two context kinds,  as in the paper. *)

  Inductive ck :=  Eᵏ | Fᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.

  (* Now we define (for each context kind) the set of values. *)

  (* For technical reasons we have to use fresh constructors; later we will *)
  (* use a coercion to identify values with the corresponding lambda terms. *)  

  Inductive val : ckind -> Type :=

  | vLam : forall {k}, var -> term -> val k
  | vVar : forall {k}, var -> val k
  | vEApp : valA -> term -> val Eᵏ
  | vFApp : valB -> val Fᵏ -> val Fᵏ

  with valA :=

  | vAVar : var  -> valA
  | vAApp : valA -> term -> valA

  with valB :=
  | vBVar : var  -> valB
  | vBApp : valB -> val Fᵏ -> valB.


  Definition value := val.
  Hint Unfold value.

  (* The coercion is a simple function that changes occurrences *)
  (* of  vLam constructors to Lam etc. *)

  Fixpoint valA_to_term v : term :=
      match v with
      | vAVar x     => Var x
      | vAApp v1 t => App (valA_to_term v1) t
      end.                    
                          
  Scheme val_Ind   := Induction for val Sort Prop
    with valB_Ind := Induction for valB Sort Prop.

  Fixpoint value_to_term {k} (v : value k) : term :=
    match v with
    | vLam x t => Lam x t
    | vVar x => Var x
    | vEApp v t => App (valA_to_term v) t
    | vFApp v1 v2 => App (valB_to_term v1) (value_to_term v2)
    end
      
  with valB_to_term v : term :=
      match v with
      | vBVar x     => Var x
      | vBApp v1 v2 => App (valB_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valA_to_term  : valA >-> term.
  Coercion valB_to_term  : valB >-> term.


  (* Here we define the set of potential redices. Here they are just *)
  (* redices: for Eᵏ kind they are lambda abstractions applied to terms or *)
  (* bang operator applied to values; for Fᵏ kind they are lambda *)
  (* abstractions applied to values or bang operator applied to terms. *)
  (* Stuck terms are not here because we defined them as values. *)

  Inductive red : ckind -> Type :=
  | rEApp : var -> term -> term -> red Eᵏ
  | rFApp : var -> term -> value Fᵏ -> red Fᵏ
  | rBangE : value Fᵏ -> red Eᵏ  
  | rBangF : term -> red Fᵏ. 
                                  
  Definition redex := red.
  Hint Unfold redex.

  (* Again we use a coercion to identify redices with the corresponding lambda terms. *)  
  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rEApp x t1 t2 => App (Lam x t1) t2
      | rFApp x t v   => App (Lam x t) (value_to_term v)
      | rBangE v       => Bang (value_to_term v)
      | rBangF t       => Bang t                       
      end.
  Coercion redex_to_term : redex >-> term.

  (* Some technicalities: it should be obvious that the two coercions are injective *)
  (* This again is a required axiom in the signature of RED_SEM module *) 

  Lemma valA_to_term_injective : 
      forall (v v' : valA), valA_to_term v = valA_to_term v' -> v = v'.

  Proof with auto.
    intro v. 
    induction v; intros; dependent destruction v'; 
    inversion H; try reflexivity.
    f_equal; apply IHv...
  Qed. 


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    intros.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valB, valB_to_term v = valB_to_term v' -> v = v');

    dependent destruction v';    inversion H; try reflexivity;
    f_equal;
    try apply valA_to_term_injective...
  Qed. 

    
  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    dependent destruction  r ; dependent destruction r';
    inversion H; try f_equal; apply (value_to_term_injective)...   
  Qed.

  
  (* Here comes the actual definition of the grammar of contexts. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *) 
  Inductive eck : ckind -> ckind -> Type := 
  | apE_r  : term -> eck Eᵏ Eᵏ       (* Eᵏ -> Eᵏ t *)
  | bang   : eck Eᵏ Fᵏ               (* Eᵏ -> ! Fᵏ *)
  | apF_r  : term -> eck Fᵏ Fᵏ       (* Fᵏ -> Fᵏ t *)
  | ap_l   : value Fᵏ -> eck Fᵏ Fᵏ.  (* Fᵏ -> v Fᵏ *) 

  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  Eᵏ.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | apE_r  t' => App t t'
      | bang => Bang t
      | apF_r  t' => App t t'
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


  Definition context : ckind -> ckind -> Type := path elem_context_kinded.

  Definition plug t {k1 k2} (c : context k1 k2) : term :=
    path_action (@elem_plug) t c.
  Notation "c [ t ]" := (plug t c) (at level 0).
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
    | Bang t' => Bang ([x:=s] t')
    end
  where "'[' x ':=' s ']' t" := (subst x s t).

  (* Example: to see how a substitution works, uncomment the lines below *)
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 1). (* [x:= \y.y] x *) *)
  (* Eval compute in [Id 1 := (Lam (Id 2) (Var (Id 2)))] Var (Id 2). (* [x:= \y.y] y *) *)


  (* Now we are ready to define the contraction. In our case this is *)
  (* either beta reduction or removal of the bang operator. *)
  (* The last rule was overlooked in the FSCD paper *)
  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rEApp x t0 t1 => Some ([x := t1] t0)
      | rFApp x t0 t1 => Some ([x := t1] t0)
      | rBangE v => Some (v:term)
      | rBangF t => Some t
      end.

  (* Decomposition of a term is a pair consisting of a reduction context and a potential redex. *)
  (* Values have no decomposition; we just report that the term is a value. *)
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



(* The two lemmas below are used in the proof of value_trivial1 below. *)
  Lemma valA_is_valE :
      forall v1 : valA, exists v2 : value Eᵏ, valA_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vVar v)...
    - exists (vEApp v1 t)...
  Qed.

  Lemma valB_is_valF :
      forall v1 : valB, exists v2 : value Fᵏ, valB_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vVar v)...
    - exists (vFApp v1 v)...
  Qed.



  (* Decomposition of a value cannot give a potential redex, it must give a value. *)
  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                             exists (v' : value k2), t = v'.
  Proof with auto using valA_is_valE, valB_is_valF. 

    intros ? ? ec t v H.
    destruct ec; dependent destruction v;  inversion H;
    dependent destruction v...
    dependent destruction v2; eexists...
    eexists...
  Qed.


  Lemma valA_is_not_Lam: forall (v : valA) x t, (v:term) <> Lam x t.
  Proof.
  intros. induction v; discriminate. 
  Qed.

  Lemma valB_is_not_Lam: forall (v : valB) x t, (v:term) <> Lam x t.
  Proof.
  intros. induction v; discriminate. 
  Qed.

  (* A value is not a redex. *)
  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    intros k v r.
    destruct r; destruct v; intro H; inversion H. 
    simpl in *. apply (valA_is_not_Lam v v0 t)...
    apply (valB_is_not_Lam v v0 t)...
    apply (valA_is_not_Lam v v0 t)...
    apply (valB_is_not_Lam v v0 t)...
  Qed.

  (* There are no other (potential) redices inside a redex; there can be only values. *)
  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof with auto.
    intros ? ? r ec t H0.

    destruct r.
    *   dependent destruction v ;  inversion H0;  dependent destruction ec. 
        eexists (vLam _ _); inversion H1;  reflexivity. inversion H1. 
    *   dependent destruction v;   inversion H0;   dependent destruction ec. 
        eexists (vLam _ _);   inversion H1; try  reflexivity.
        inversion H1.  exists v0...
    *   dependent destruction ec;  inversion H0.
         exists v...
    *   dependent destruction ec;  inversion H0.            
  Qed.

  (* This ends the definition of the reduction sematnics *)
End Lam_cbn_strict_PreRefSem.


(* Although a reduction semantics implicitly contains reduction strategy, our implementation 
   requires an explicit definition of this strategy. So now we define the reduction strategy.  *)


(* The module type REF_STRATEGY is defined in the file refocusing/refocusing_semantics.v. *)
Module Lam_cbn_strict_Strategy <: REF_STRATEGY Lam_cbn_strict_PreRefSem.

  Import Lam_cbn_strict_PreRefSem.

  (* Here we define the two functions: up arrow and down arrow. *)
  (* We start by defining the type returned by these functions.  *)
  (* They return that the input term is either a redex (ed_red) *)
  (* or a value (ed_val) or that we have to continue searching  *)
  (* inside a subterm (ed_dec) *)  
  Inductive elem_dec k : Type :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.


  
  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)  
  (* The function says what to do when we try to evaluate a term.  In
  the case of Eᵏ-strategy the first rule says that when we evaluate an
  application, we start by evaluating the left argument (the calling
  function). The second rule says that a variable is a value (so we do
  not evaluate it). Similarly, the third rule says that when we
  evaluate a lambda abstraction, we already have a value. The last
  rule says that when we evaluate bang applied to a term, we should
  change the strategy to Fᵏ and decompose the term. In the case of
  Fᵏ-strategy the first three rules say the same: we evaluate the
  first argument of an application, variables and lambda abstractions
  are values. The last rule is different: it says that bang operator
  applied to a term is a redex (intuitively, in Fᵏ strategy we are in
  call-by-value, so bang has no meaning and can be removed).*)
  Definition dec_term t k : elem_dec k :=
    match k with
    |  Eᵏ =>     match t with
                 | App t1 t2 => ed_dec  Eᵏ t1 (apE_r t2)   (*  [t1 t2]_E ⇓ [t1]_E t2 *)
                 | Var x     => ed_val (vVar x)                         (* [x]_E ⇓ V *)
                 | Lam x t1  => ed_val (vLam x t1)                   (* [\x.t]_E ⇓ V *)
                 | Bang t'  => ed_dec Fᵏ t' bang                  (*[!t]_E ⇓ ! [t]_F *)
                 end
    |  Fᵏ =>     match t with
                 | App t1 t2 => ed_dec  Fᵏ t1 (apF_r t2)   (*  [t1 t2]_F ⇓ [t1]_F t2 *)
                 | Var x     => ed_val (vVar x)                         (* [x]_F ⇓ V *)
                 | Lam x t1  => ed_val (vLam x t1)                   (* [\x.t]_F ⇓ V *)
                 | Bang t'  => ed_red (rBangF t')                       (*[!t]_F ⇓ R *)
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
  (* It is used to decompose a context.  *)

  (* Here we would like to define this function as follows.
  
  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec with 
    | apE_r t => [...]
    | bang => ed_red (rBangE v)
    | apF_r t => ed_dec Fᵏ t (ap_l v)
    | ap_l v' => [...]
    end.

  Unfortunately, Coq is not able to infer whether k/k' is Eᵏ or Fᵏ,
  and we have to do some dirty tricks. 


  This function says what to do when we finish evaluation of a
  subterm.  Here the first rule says what to do when we finish
  evaluation of the first argument of application according to
  Eᵏ-strategy. If the obtained value is a lambda abstraction, we
  contract (beta-reduce); otherwise we just report we have a value;
  the case of vFApp is not possible in Eᵏ-strategy, but we have to
  handle it somehow to make Coq not complain about non-exhaustive
  pattern maching. The second rule says what to do when we finish the
  evaluation of an argument of bang: this is possible only in
  Fᵏ-strategy and we reduce. The third rule applies when we finish the
  evaluation of the calling function in Fᵏ-strategy: we start the
  evaluation of the argument (by decomposing it).  The last rule
  says what to do when we finish evaluation of the argument of
  application in Fᵏ-strategy: if the first argument is a lambda
  abstraction, we reduce; otherwise we report a value. *)


  
  Definition dec_context  {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec in eck k k' return value k' -> elem_dec k with
    | apE_r t =>  (fun v => match (v:value Eᵏ) with
                            | vLam x t'   => ed_red (rEApp x t' t)        (* [[\x.t1]_E t2]_E ⇑ R *)
                            | vVar x      => ed_val (vEApp (vAVar x) t)        (* [[a]_E t]_E ⇑ V *)
                            | vEApp v' t' => ed_val (vEApp (vAApp v' t') t)    (* [[a]_E t]_E ⇑ V *)
                            | vFApp v' t  => ed_val (vVar (Id 1))              (* impossible case *)
                   end)
    | bang    =>  (fun v => ed_red  (rBangE v))                                (* [! [v]_F]_E ⇑ R *)
    | apF_r t =>  (fun v => ed_dec Fᵏ t (ap_l v))                       (* [ [v]_F t]_F ⇑ v [t]_F *)
    | ap_l v' => (fun v => match (v': value Fᵏ) with
                           | vLam x t => ed_red  (rFApp x t v)             (* [\x.t [v]_F ]_F ⇑ R *)
                           | vVar x     => ed_val (vFApp (vBVar x) v)          (* [b [v]_F]_F ⇑ V *)
                           | vEApp v' t => ed_val (vVar (Id 1))                (* impossible case *)
                           | vFApp v' t => ed_val (vFApp (vBApp v' t) v)       (* [b [v]_F]_F ⇑ V *)
                   end)
    end v.




  (* The two pairs (term, context) before and after decomposition represent the same term. *)
  Lemma dec_context_correct :         forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r        => ec:[v] = r
      | ed_val v'       => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.

  Proof with auto.
    intros ? ? ec v.
    destruct ec.
    * dependent destruction v; simpl...  
    * dependent destruction v; simpl...
    * dependent destruction v; simpl... 
    * dependent destruction v0; simpl...
  Qed.

  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)

  (* The set of all elementary contexts generated from  nonterminal k *)
  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop :=
    let (_, ec)  := ec  in
    let (_, ec0) := ec0 in
    match ec, ec0 with 
    | ap_l _, apF_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
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
          dec_term t k = ed_dec _ t' ec -> so_maximal ec t.
  Proof.
    intros k k' t t' ec H ec' H0. 
    destruct t, ec; dependent destruction ec'; destruct k';
    inversion H; inversion H0.
  Qed.

  (* If the up-arrow function returns a redex, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from the minimal element. *) 
  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                                         (ec : elem_context_kinded k k'),
          dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof.
    intros k k' ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    inversion H; try
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
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
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
eexists. eauto. 
eexists. eauto. 


  Qed.

End Lam_cbn_strict_Strategy.


(* The refocusable semantics is composed from the reduction semantics and the reduction strategy *)
Module Lam_cbn_strict_RefSem := RedRefSem Lam_cbn_strict_PreRefSem Lam_cbn_strict_Strategy.



Require Import refocusing_machine.

(* And the abstract machine is generated from this semantics *)
Module Lam_cbn_strict_EAM := RefEvalApplyMachine Lam_cbn_strict_RefSem.

Import Lam_cbn_strict_PreRefSem.

Import Lam_cbn_strict_EAM.

(* An example computation of the generated machine *)

Require Import abstract_machine_facts.
Module Lam_cbn_strict_sim := DetAbstractMachine_Sim Lam_cbn_strict_EAM.
Import Lam_cbn_strict_sim.

Definition x := Id 1.
Definition y := Id 2.
Definition xx:= (Lam x (App (Var x) (Var x))).
Definition id:= (Lam x (Var x)).
Definition id_y:= (Lam y (Var y)).
Definition t:= (App xx (App id id_y)).
Definition t':= Bang (App xx (App id id_y)).

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

Eval compute in list_configurations  t 25 .
Eval compute in list_configurations  t' 25 .

(* and the complete machine *)
Print Lam_cbn_strict_EAM.

