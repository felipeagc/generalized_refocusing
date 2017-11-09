(* Lambda calculus with the call-by-need reduction strategy *)
(* version of Danvy & Zerny PPDP13, 'revised cbneed λ_let-calculus of Fig. 5 *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.

(* Here we define the reduction semantics. *)
(* The module type PRE_REF_SEM is defined in the file *)
(*     refocusing/refocusing_semantics.v *)
(* It inherits part of the signature from RED_SEM defined in *)
(*     reduction_semantics/reduction_semantics.v *)

Module Lam_cbnd_PreRefSem <: PRE_REF_SEM.

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

  Inductive ck := E.
  Definition ckind := ck.
  Hint Unfold  ckind.


  (* Here we define the language of interest: lambda calculus. *)
  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr
  | Let : var -> expr -> expr -> expr
  | LetNd : forall x, expr -> neutral x -> expr (* let x := e in E[x] *)
  with
    neutral : var -> Type := (* neutrals parameterized by head variable *)
  | nVar : forall x : var, neutral x
  | nApp : forall x : var, neutral x -> expr -> neutral x
  | nSub : forall x y, x <> y -> expr -> neutral y -> neutral y (* let x = e in n_y *)
  | nNeuSub : forall x y, neutral y -> neutral x -> neutral y. (* let x := n_y in n_x *)

Notation " t @ s " := (App t s) (at level 40).
Notation " # x " := (Var x) (at level 7).
Notation " t [ x / s ] " := (Let x s t) (at level 45).
Notation " 'λ'  x , t " := (Lam x t) (at level 50, x ident).

  Inductive sub : ckind -> Type :=
  | subMt : sub E
  | subCons : var -> expr -> sub E -> sub E.

  Definition term := expr.
  Hint Unfold term.

  Inductive val : ckind -> Type :=
  | vLam : var -> term  -> val E.

  Fixpoint val_to_term {k} (v : val k) : term :=
      match v with
      | vLam x t => Lam x t
      end.

  Coercion val_to_term : val >-> term.
  
  Inductive answer : ckind -> Type :=
  | ansVal : val E -> sub E -> answer E (* (λ x . t) [y/s...] *)
  | ansNeu : forall x, neutral x -> answer E. (* all neutrals are open terms and (intermediate) answers *)
  
  Definition value := answer. (* in this setting neutrals cannot be stuck terms *)
  Hint Unfold value.

  Fixpoint sub_to_term {E} (s : sub E) (t : term) :=
  match s with
  | subMt => t
  | subCons x r s' => Let x r (sub_to_term s' t)
  end.

  Fixpoint neutral_to_term {x} (n : neutral x) : term :=
  match n with
  | nVar x => Var x
  | nApp _ n t => App (neutral_to_term n) t
  | nSub x y _ e n => Let x e (neutral_to_term n)
  | nNeuSub y x n1 n2 => LetNd y (neutral_to_term n1) n2
  end.
    
  Fixpoint answer_to_term {k} (a : answer k) : term :=
  match a with
  | ansVal v s => sub_to_term s v
  | ansNeu _ n   => neutral_to_term n
  end.
      
  Coercion answer_to_term : answer >-> term.
  Coercion neutral_to_term : neutral >-> term.

  (* Here we define the set of potential redices. *)
  
  Inductive red : ckind -> Type :=
  | rApp : val E -> sub E -> term -> red E
  | rSub : forall x, neutral x -> val E -> sub E -> red E
  | rSubNd : forall x, term -> neutral x -> red E.
   
  Definition redex := red.
  Hint Unfold redex.
 
  Reserved Notation "'[' x ':=' s ']' t" (at level 20).

  Fixpoint subst (x:var) (s:term) (t:term) : term :=
    match t with
    | Var x' => 
        if eq_var x x' then s else t
    | Lam x' t1 => 
        Lam x' (if eq_var x x' then t1 else ([x:=s] t1)) 
    | App t1 t2 => 
        App ([x:=s] t1) ([x:=s] t2)
    | Let x' r u => Let x' (subst x s r) (if eq_var x x' then u else [x:=s] u)
    | LetNd x' r n => 
      LetNd x' (subst x s r) (if eq_var x x' then n else n)
    end
 
  where "'[' x ':=' s ']' t" := (subst x s t).

  Fixpoint subst_neutral (x:var) (n:neutral x) (s : term) : term :=
    match n with
    | nVar y => s
    | nApp v n t => App (subst_neutral v n s) t
    | nSub y x' _ e n => Let x e (subst_neutral x' n s)
    | nNeuSub y x' n n' => LetNd y (subst_neutral x' n s) n'    
    end.

  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp v s t => App (sub_to_term s v) t
      | rSub x n v s => LetNd x (sub_to_term s (val_to_term v)) n
      | rSubNd x t n => Let x t (neutral_to_term n)
      end.
      
  Coercion redex_to_term : redex >-> term.

  (* This again is a required axiom in the signature of RED_SEM module *) 
  Lemma val_to_term_injective : 
      forall {k} (v v' : val k), val_to_term v = val_to_term v' -> v = v'.

  Proof with auto.
    destruct v. intros.
    dependent destruction v'.   inversion H. reflexivity. 
  Qed.


  Lemma sub_to_term_val_injective : 
    forall {k} (s s' : sub k) (v v' : val E), 
    sub_to_term s v = sub_to_term s' v' -> s = s' /\ v = v'.

  Proof with auto.
  intros k s s' v v' H. 
  induction s; dependent destruction s'; inversion H.
  destruct v; dependent destruction v'; inversion H1...
  destruct v0; dependent destruction s'; inversion H1...
  dependent destruction s; destruct v'; inversion H1; split...
  split; f_equal; elim IHs with s'...
  Qed.  



  Lemma sub_to_term_var_injective : 
    forall {k} (s s' : sub k) x x', 
    sub_to_term s (Var x) = sub_to_term s' (Var x') -> s = s' /\ x = x'.

  Proof with auto.
  intros k s s' x x' H. 
  induction s; dependent destruction s'; inversion H...
  elim IHs with s'; intros; subst...
 Qed.  

  
  Lemma sub_to_term_letnd_injective : 
    forall {k} (s s' : sub k) x y e1 e2 nx ny, 
    sub_to_term s (LetNd x e1 nx) = sub_to_term s' (LetNd y e2 ny) -> s = s' /\ e1 = e2 /\ x = y /\ nx ~= ny.

  Proof with auto.
  intros k s s' x y e1 e2 nx ny H. 
  induction s; dependent destruction s'; inversion H...
  elim IHs with s'; intros; subst...
 Qed.  

  
  Lemma sub_to_term_neutral : 
    forall {k} (s s' : sub k) (v : val E) {x} (n : neutral x), 
    sub_to_term s v = sub_to_term s' n -> False.

  Proof with auto.
  induction s; simpl; intros.
  destruct v; destruct s'; destruct n; discriminate.
  destruct s'. destruct n; simpl in *; try discriminate.
  inversion H. elim IHs with subMt v0 y n0...
  inversion H. elim (IHs _ _ _ _ H3).
  Qed.

  Lemma sub_to_term_var : 
    forall {k} (s s' : sub k) x (v : val E), 
    sub_to_term s v = sub_to_term s' (Var x) -> False.

  Proof with auto.
  induction s; simpl; intros.
  destruct v; destruct s'; discriminate.
  destruct s'. discriminate.
  inversion H. elim IHs with s' x v0...
  Qed.

  Lemma neutral_to_term_injective : 
    forall {x y} (n : neutral x) (n' : neutral y), 
    neutral_to_term n = neutral_to_term n' -> n ~= n' /\ x = y.

  Proof with auto.
    induction n; intros; destruct n'; try discriminate;
    inversion H; subst;
    try elim IHn with n'; intros; subst; try split...
    dependent rewrite H0...
    subst; rewrite proof_irrelevance with (x0 <> y) n n1...
    subst; dependent rewrite H3.    elim IHn1 with n'1; intros; subst...
    dependent rewrite H0; auto. 
    elim IHn1 with n'1...
  Qed.
(*
 Lemma neutral_to_term_injective : 
    forall {x} (n n' : neutral x), 
    neutral_to_term n = neutral_to_term n' -> n = n'.

  Proof with auto.
    induction n; intros; destruct n'; try discriminate...
    inversion H. rewrite IHn with n'...
    inversion H. rewrite IHn with n'...
    inversion H; subst. 
    rewrite proof_irrelevance with (x0 <> y) n n1...
    inversion H. dependent rewrite H3. rewrite IHn1 with n'1...
  Qed.
*)

  Lemma answer_to_term_injective : 
    forall {k} (a a' : answer k), 
    answer_to_term a = answer_to_term a' -> a = a'.

  Proof with auto.
    destruct a; dependent destruction  a'; intros...
    f_equal; elim sub_to_term_val_injective with s s0 v v0...
    elim sub_to_term_neutral with s subMt v _ n...
    elim sub_to_term_neutral with s subMt v _ n...
    inversion H.
    elim neutral_to_term_injective with n n0; intros; subst...
    rewrite H0...
  Qed.



  Definition value_to_term {k} (a : value k) := answer_to_term a.
  
  Lemma value_to_term_injective : forall {k} (a a' : value k), 
    value_to_term a = value_to_term a' -> a = a'.
  Proof with auto.
    intros; apply answer_to_term_injective...
  Qed.
  

  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct r ; dependent destruction r';
    inversion H; subst.
    dependent destruction v; dependent destruction v0...
    f_equal; elim sub_to_term_val_injective with s s0 (vLam v t) (vLam v0 t0); intros; subst...
    elim sub_to_term_val_injective with s s0 v v0; intros; subst...
    elim neutral_to_term_injective with n n0; intros; subst...
  Qed.
  

  Inductive eck : ckind -> ckind -> Set := 
  | ap_r  : term -> eck E E
  | in_let : var -> term -> eck E E
  | let_var : forall x, neutral x -> eck E E. 
  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  E.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      | in_let x s => Let x s t
      | let_var x n => LetNd x t n
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


  (* A reduction context is a stack of elementary contexts. *)
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


  (* Now we are ready to define the contraction. *)
  
  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp (vLam x r) s t => Some (sub_to_term s (Let x t r))
      | rSub x n v s => Some (sub_to_term s (Let x (val_to_term v) (subst_neutral x n v)))
      | rSubNd x t n => Some (LetNd x t n)
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
  Proof with auto.
    intros ? ? ec t v H.
    destruct ec;   dependent destruction v; inversion H; 
    try (dependent destruction s; 
    dependent destruction v; discriminate).
    destruct n; try discriminate.
    exists (ansNeu x n); inversion H; subst...
    dependent destruction s; dependent destruction v; try discriminate.
    injection H1; intros; subst...
    exists (ansVal (vLam v t1) s)...
    destruct n; try discriminate.
    injection H; intros; subst;
    exists (ansNeu _ n0); simpl; auto.
    destruct n0; try discriminate.
    inversion H1; subst...
    exists (ansNeu _ n0_1)...
  Qed.
  

  (* A value is not a redex. *)

  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    intros k v r.
    destruct r; destruct v; intro H; inversion H;
    try (dependent destruction s0; 
    dependent destruction v; try discriminate).
    destruct n; inversion H1; subst;
    elim sub_to_term_neutral with s subMt v0 x n...
    destruct n0; try discriminate; inversion H; intros; subst.
    elim sub_to_term_neutral with s subMt v0 _ n0_1...
    dependent destruction s;
    inversion H1; intros; subst...
    dependent destruction v; discriminate.
    elim sub_to_term_neutral with s subMt v _ n...
    destruct n0; try discriminate.
    inversion H1; subst.
    elim neutral_to_term_injective with n1 n...
  Qed.

  (* There are no other potential redices inside a potential redex; *)
  (* there can be only values. *)
  Lemma redex_trivial1 :   forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
       ec:[t] = r -> exists (v : value k'), t = v.

  Proof with auto.
      intros ? ? r ec t H.
    destruct ec; dependent destruction r;
    inversion H; 
    subst.
    exists (ansVal v s)...
    exists (ansNeu _ n)...
    exists (ansVal v s)...
  Qed.

End Lam_cbnd_PreRefSem.


(* The module type REF_STRATEGY is defined in the file *)
(*     refocusing/refocusing_semantics.v. *)
Module Lam_cbn_Strategy <: REF_STRATEGY Lam_cbnd_PreRefSem.

  Import Lam_cbnd_PreRefSem.

  (* Here we define the two functions: up arrow and down arrow. *)
  Inductive elem_dec k : Set :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.

  
  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)  

  Definition dec_term t k : elem_dec k :=
    match k with E => 
                 match t with
                 | App t1 t2 => ed_dec  E t1 (ap_r t2)
                 | Var x     => ed_val (ansNeu _ (nVar x))
                 | Lam x t1  => ed_val (ansVal (vLam x t1) subMt)
                 | Let x t1 t2 => ed_dec E t2 (in_let x t1)
                 | LetNd x t n => ed_dec E t (let_var x n)
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


  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec, v with
    | ap_r t, ansVal v' s => ed_red  (rApp v' s t)
    | ap_r t, ansNeu _ n => ed_val (ansNeu _ (nApp _ n t))
    | in_let x t, ansVal v' s => ed_val (ansVal v' (subCons x t s))
    | in_let x t, ansNeu y n => 
      (match eq_var x y with
      | left peq => ed_red (rSubNd y t n) (* redex! *)
      | right pneq => ed_val (ansNeu y (nSub x _ pneq t n))
      end) 
    | let_var x n, ansVal v s => ed_red (rSub _ n v s) 
    | let_var x n, ansNeu _ n' => ed_val (ansNeu _ (nNeuSub x _ n' n))
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
    case_eq (eq_var v0 x); intros; subst; auto.
  Qed.


  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)

  Inductive elem_context_in k : Set :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  (* In the case of call-by-name the order is trivial. *)
  (* We have only one production in the grammar and there are no overlapping *)
  (* elementary contexts. There is simply nothing to compare. *)
  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop := False.
 
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

  compute; do 2 right; split; auto.
  simpl in *.
  injection H5; intros; subst.
  reflexivity.

  compute; do 2 right; split; auto.
  simpl in *.
  injection H5; intros; subst.
  symmetry.
  dependent destruction H.
  reflexivity.
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
    destruct k, t, ec'; inversion H;  subst; inversion H0; intro HHH; inversion HHH.
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
    try discriminate; 
    solve [simpl in *;
    case_eq (eq_var v0 x); intros; subst; rewrite H0 in H; discriminate].
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
Module Lam_cbn_RefSem := RedRefSem Lam_cbnd_PreRefSem Lam_cbn_Strategy.


(* And the abstract machine is generated from this semantics *)
Require Import refocusing_machine.
Module Lam_cbn_EAM := RefEvalApplyMachine Lam_cbn_RefSem.


(* An example computation of the generated machine *)
Import Lam_cbnd_PreRefSem.
Import Lam_cbn_EAM.
Require Import abstract_machine_facts.
Module Lam_cbn_sim := DetAbstractMachine_Sim Lam_cbn_EAM.
Import Lam_cbn_sim.


Definition x  := Id 1.
Definition xx := λ x , # x @ # x.
Definition id := λ  x , # x.
Definition t := xx @ id.



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

Eval compute in list_configurations  t 50.


(* and the complete machine *)
Print Lam_cbn_EAM.


