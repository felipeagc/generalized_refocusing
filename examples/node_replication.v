(* Lambda calculus with the call-by-need reduction strategy *)
(* version of Danvy & Zerny PPDP13, 'revised cbneed λ_let-calculus of Fig. 5 *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.
Require Import empty_search_order.

(* Here we define the reduction semantics. *)
(* The module type PRE_RED_SEM is defined in the file *)
(*     reduction_semantics/reduction_semantics.v *)
(* It is a RED_SEM without totality of decompose *)

Module Lam_cbnd_PreRefSem <: PRE_RED_SEM.

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

  (* The main ingredient of a reduction semantics is a grammar of contexts.  *)
  (* We start with nonterminal symbols, which are called here "context kinds". *)

  (* Weak call-by-need is a uniform strategy, so one context kind E is enough. *)

  Inductive ck := L | LL | N.
  Definition ckind := ck.
  Hint Unfold  ckind.

  (* Here we define the language of interest: lambda-let calculus.  *)
  (* Needys parameterized by a variable x are evaluation contexts *)
  (* with x plugged in the hole. Thus they are neutral terms with *)
  (* the variable x being needed. *)

  Inductive expr :=
  | Var       : var -> expr                                 (* variable *)
  | Lam       : var -> expr -> expr                         (* lambda abstraction *)
  | App       : expr -> expr -> expr                        (* application *)

  | ExpSubst  : expr -> var -> expr -> expr                 (* explicit substitution t[x / u] *)
                                                            (* will evaluate t first *)

  | ExpSubstS : forall x : var, needy x -> expr -> expr     (* strict explicit substitution n_x[x / u] *)
                                                            (* will evaluate u first *)

  | ExpDist   :                                             (* explicit distributor t[x // λy.u] *)
      expr -> var -> var -> expr -> expr                    (* will evaluate t first *)

  | ExpDistS  : forall x : var,                             (* strict explicit distributor n_x[x // λy.u] *)
      needy x -> var -> expr -> expr                        (* will evaluate u first *)

  with
    needy : var -> Type := (* needys parameterized by head variable *)
    | nVar       : forall x : var, needy x
    | nApp       : forall x : var, needy x -> expr -> needy x       (* (n_x t) *)

    | nExpSubst  : forall x y,
        x <> y -> needy x -> expr -> needy x (* n_x[y / u] *)
    | nExpSubstS : forall x y,
        needy y -> needy x -> needy x        (* strict n_y[y / n_x] *)

    | nExpDist  : forall x y z : var,                               (* n_x[y // λz.u] *)
        x <> y -> needy x -> expr -> needy x
    | nExpDistS : forall x y z : var,                               (* strict n_y[y // λz.n_x] *)
        y <> z -> z <> x -> needy y -> needy x -> needy x.

  Definition term := expr.
  Hint Unfold term.

  Notation " t @ s " := (App t s) (at level 40).
  Notation " # x " := (Var x) (at level 7).
  Notation " t [ x / u ] " := (ExpSubst x u t) (at level 45).
  Notation " t [ x '//' 'λ' y , u ] " := (ExpDist x y u t) (at level 46).
  Notation " 'λ'  x , t " := (Lam x t) (at level 50).



  Inductive pure_term :=
  | PVar : var -> pure_term                        (* variable *)
  | PLam : var -> pure_term -> pure_term           (* lambda abstraction *)
  | PApp : pure_term -> pure_term -> pure_term.    (* application *)

  Fixpoint pure_term_to_term (p : pure_term) : term :=
      match p with
      | PVar x => Var x
      | PLam x t => Lam x (pure_term_to_term t)
      | PApp t s => App (pure_term_to_term t) (pure_term_to_term s)
      end.

  (* v *)
  Inductive val : ckind -> Type :=
  | vLam : var -> pure_term -> val N.

  Fixpoint val_to_term {k} (v : val k) : term :=
      match v with
      | vLam x t => Lam x (pure_term_to_term t)
      end.

  Coercion val_to_term : val >-> term.



  (* L - Lists context *)
  Inductive lCtx : ckind -> Type :=
  | lEmpty : lCtx L                             (* <> *)
  | lSubst : lCtx L -> var -> term -> lCtx L    (* L[x / u] *)
  | lDist  : lCtx L -> var -> var -> term -> lCtx L.  (* L[x // λy.u] *)

  (* T - Linear Cut Values *)
  Inductive linear_cut_val : Type :=
  | lcLam : var -> llCtx LL -> pure_term -> linear_cut_val (* λx.LL<p> *)
  with
    (* LL - Commutative lists context *)
    llCtx : ckind -> Type :=
    | llEmpty : llCtx LL                                 (* <> *)
    | llSubst : llCtx LL -> var -> pure_term -> llCtx LL (* LL[x / p] *)
    | llDist  : llCtx LL -> var -> linear_cut_val -> llCtx LL.  (* LL[x // T] *)

  (* U - Restricted terms *)
  (* maybe we're gonna need a needy variation like expr *)
  Inductive restricted_term : Type :=
  | rtVar : var -> restricted_term (* x *)
  | rtVal : val N -> restricted_term (* v *)
  | rtApp : restricted_term -> restricted_term -> restricted_term  (* UU *)
  | rtSubst : restricted_term -> var -> restricted_term -> restricted_term (* U[x / U] *)
  (* | rtSubstA : forall x, needy_restricted_term x -> restricted_term -> restricted_term (* U[x / U] *) *)
  | rtDist : restricted_term -> var -> linear_cut_val -> restricted_term (* U[x // T] *)
      (* | rtDistA : forall x, needy_restricted_term x -> needy_restricted_term -> linear_cut_val -> restricted_term (* U[x // T] *) *)
  . 



  (* y ∈ dom(LL) *)
  Fixpoint is_in_dom_ll (ll : llCtx LL) (v : var): Prop :=
    match ll with
    | llEmpty => False
    | llSubst l v' _ => if eq_var v v' then True else is_in_dom_ll l v
    | llDist l v' _ => if eq_var v v' then True else is_in_dom_ll l v
    end.

  (* v ∈ fv(p) *)
  Fixpoint p_has_free_occurrence (p : pure_term) (v : var) : Prop :=
    match p with
    | PVar v' => if eq_var v v' then True else False
    | PLam v' p' => (if eq_var v v' then False else p_has_free_occurrence p' v)
    | PApp p1 p2 => (p_has_free_occurrence p1 v) /\ (p_has_free_occurrence p2 v)
    end.

  (* v ∈ fv(LL) *)
  Fixpoint ll_has_free_occurrence (ll : llCtx LL) (v : var) : Prop :=
    match ll with
    | llEmpty => False
    | llSubst l x p => (if eq_var x v then False else ll_has_free_occurrence l v) \/
                            p_has_free_occurrence p v
    | llDist l x t => (if eq_var x v then False else ll_has_free_occurrence l v) \/
                            t_has_free_occurrence t v
    end
  with
    (* v ∈ fv(T) *)
    t_has_free_occurrence (t : linear_cut_val) (v : var) : Prop :=
      match t with
      | lcLam x ll p => if eq_var x v then False else ll_has_free_occurrence ll v
      end.

  (* Check property: T := λx.LL<p> where y ∈ dom(LL) ⇒ y ∈ fv(p) *)
  Definition t_is_good (t : linear_cut_val): Prop :=
    match t with
    | lcLam x ll p => forall y : var, is_in_dom_ll ll y -> p_has_free_occurrence p y
    end.

  (* Check property: LL := LL[x//T] where x ∉ fv(LL) *)
  Definition ll_is_good (ll : llCtx LL): Prop :=
    match ll with
    | llDist ll' x t => not (ll_has_free_occurrence ll' x)
    | _ => True
    end.



  (* N - Answer context *)
  (* Inductive ansCtx : ckind -> Type := *)
  (* | ansCtxEmpty : ansCtx N (* <> *) *)
  (* | ansCtxApp : ansCtx N -> term -> ansCtx N (* Nt *) *)
  (* | ansCtxSubst : ansCtx N -> var -> term -> ansCtx N (* N[x / t] *) *)
  (* | ansCtxDist : ansCtx N -> var -> var -> term -> ansCtx N (* N[x // λy.t] *) *)
  (* | ansCtxPlugSubst : ansCtx N -> var -> ansCtx N -> ansCtx N. (* N<<x>>[x/N] *) *)

  Inductive answer : ckind -> Type :=
  | ansVal : val N -> lCtx L -> answer N
  | ansNd : forall x, needy x -> answer N.

  (* It should be made clear here that the values in this *)
  (* implementation of refocusing are not the same as values in the Danvy *)
  (* and Zerny's paper. The implementation requires all useful normal forms *)
  (* to be values. By "useful" we mean that such a normal form put into *)
  (* some reduction context does participate in further computation. Stuck *)
  (* term thtat remain stuck in all reduction contexts need not be *)
  (* values. *)



  (* In this setting needys cannot be stuck terms. Needys are *)
  (* intermediate values and we have to treat them as values *)
  (* Hence the category of values mast contain both answers  *)
  (* and needys *)
  Definition value := answer.
  Hint Unfold value.

  (* A function for plugging a term to an answer context *)
  Fixpoint lCtx_plug {L} (s : lCtx L) (t : term) :=
  match s with
  | lEmpty => t
  | lSubst s' x r => ExpSubst (lCtx_plug s' t) x r
  | lDist s' x y r => ExpDist (lCtx_plug s' t) x y r
  end.

  (* A function for plugging a term to an answer context *)
  (* Fixpoint ansCtx_plug {N} (s : ansCtx N) (t : term) := *)
  (* match s with *)
  (* | ansCtxEmpty => t *)
  (* | ansCtxApp s' r => App (ansCtx_plug s' t) r *)
  (* | ansCtxSubst s' x r => ExpSubst (ansCtx_plug s' t) x r *)
  (* | ansCtxDist s' x y r => ExpDist (ansCtx_plug s' t) x y r *)
  (* | ansCtxPlugSubst s1 x s2 => ExpSubst (ansCtx_plug s1 (Var x)) x (ansCtx_plug s2 t) *)
  (* end. *)


  Fixpoint needy_to_term {x} (n : needy x) : term :=
  match n with
  | nVar x => Var x
  | nApp _ n t => App (needy_to_term n) t
  | nExpSubst _ y _ n e => ExpSubst (needy_to_term n) y e
  | nExpSubstS _ y n_y n_x => ExpSubstS y n_y (needy_to_term n_x)

  | nExpDist _ y z _ n_x e => ExpDist (needy_to_term n_x) y z e
  | nExpDistS _ y z _ neq_zx n_y n_x => ExpDistS y n_y z (needy_to_term n_x)
  end.


  Fixpoint answer_to_term {k} (a : answer k) : term :=
  match a with
  | ansVal v s => lCtx_plug s v
  | ansNd _ n   => needy_to_term n
  end.

  Coercion answer_to_term : answer >-> term.
  Coercion needy_to_term : needy >-> term.


  (* Here we define the set of potential redices. *)
  (* Actually, they are just redices as defined in the paper *)
  Inductive red : ckind -> Type :=
  | rApp : lCtx L -> val N -> term -> red N            (* L<v> u *)
  | rSpl : forall x, needy x -> val N -> lCtx L -> red N (* N<<x>>[x/L<λy.p>] *)
  | rLs  : forall x, needy x -> val N -> red N.          (* N<<x>>[x//v] *)

  Definition redex := red.
  Hint Unfold redex.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp l v t => App (lCtx_plug l v) t
      | rSpl x n v s => ExpSubstS x n (lCtx_plug s (val_to_term v))
      | rLs x n v => ExpSubst (needy_to_term n) x (val_to_term v)
      end.

  Coercion redex_to_term : redex >-> term.


  (* This again is a required axiom in the signature of RED_SEM module *)
  Lemma pure_term_to_term_injective :
      forall (v v' : pure_term), pure_term_to_term v = pure_term_to_term v' -> v = v'.
  Proof with auto.
    induction v. intros. destruct v'. inversion H...
    inversion H...
    inversion H...

    dependent destruction v'.
    intros. inversion H.
    intros. inversion H.
    apply IHv in H2.
    rewrite H2. reflexivity.

    intros. inversion H.

    dependent destruction v'.
    intros. inversion H.
    intros. inversion H.

    intros. inversion H.
    apply IHv1 in H1. apply IHv2 in H2.
    rewrite H1. rewrite H2.
    reflexivity.
  Qed.

  Lemma val_to_term_injective :
      forall {k} (v v' : val k), val_to_term v = val_to_term v' -> v = v'.
  Proof with auto.
    destruct v. intros.
    dependent destruction v'.  inversion H.
    apply pure_term_to_term_injective in H2.
    rewrite H2. reflexivity.
  Qed.


  Lemma lCtx_plug_val_injective :
    forall {k} (s s' : lCtx k) (v v' : val N),
    lCtx_plug s v = lCtx_plug s' v' -> s = s' /\ v = v'.
  Proof with auto.
    intros k s s' v v' H.
    induction s; dependent destruction s'; inversion H...
    destruct v; dependent destruction v'; inversion H1...
    apply pure_term_to_term_injective in H3; rewrite H3; auto.

    destruct v0; dependent destruction s'; inversion H...
    destruct v1; dependent destruction s'; inversion H...

    dependent destruction s; destruct v'; inversion H1; split...
    split; f_equal; elim IHs with s'...

    dependent destruction s; destruct v'; inversion H1; split...
    split; f_equal; elim IHs with s'...
  Qed.


  Lemma lCtx_plug_var_injective :
    forall {k} (s s' : lCtx k) x x',
    lCtx_plug s (Var x) = lCtx_plug s' (Var x') -> s = s' /\ x = x'.
  Proof with auto.
    intros k s s' x x' H.
    induction s; dependent destruction s'; inversion H...
    split; f_equal; elim IHs with s'...
    split; f_equal; elim IHs with s'...
  Qed.


  Lemma lCtx_plug_needy :
    forall {k} (s s' : lCtx k) (v : val N) {x} (n : needy x),
    lCtx_plug s v = lCtx_plug s' n -> False.
  Proof with auto.
    induction s; simpl; intros.
    destruct v; destruct s'; destruct n; discriminate.
    destruct s'. destruct n; simpl in *; try discriminate.
    inversion H; elim IHs with lEmpty v0 x n0...
    inversion H; elim (IHs _ _ _ _ H1).
    inversion H.
    destruct s'. destruct n; simpl in *; try discriminate.
    inversion H. elim IHs with lEmpty v1 x n0...
    inversion H; elim (IHs _ _ _ _ H1).
    inversion H; elim (IHs _ _ _ _ H1).
  Qed.

  Lemma lCtx_plug_var :
    forall {k} (s s' : lCtx k) x (v : val N),
    lCtx_plug s v = lCtx_plug s' (Var x) -> False.
  Proof with auto.
    induction s; simpl; intros.
    destruct v; destruct s'; discriminate.
    destruct s'. discriminate.
    inversion H. elim IHs with s' x v0...
    inversion H. 
    destruct s'. discriminate.
    inversion H. elim IHs with s' x v1...
    inversion H. elim IHs with s' x v1...
  Qed.

  Lemma needy_to_term_injective :
    forall {x y} (n : needy x) (n' : needy y),
    needy_to_term n = needy_to_term n' -> n ~= n' /\ x = y.
  Proof with auto.
    induction n; intros; destruct n'; try discriminate;
    inversion H; subst;
    try elim IHn with n'; intros; subst; try split...
    dependent rewrite H0...

    subst; rewrite proof_irrelevance with (x0 <> y) n n1...
    elim IHn2 with n'2; intros; subst...

    dependent rewrite H0; auto.

    elim IHn2 with n'2...

    subst. rewrite proof_irrelevance with (x0 <> y) n n1...

    elim IHn2 with n'2; intros; subst...
    subst. rewrite proof_irrelevance with (y <> z0) n n1...
    subst. rewrite proof_irrelevance with (z0 <> x0) n0 n2...
    subst. 
    (* rewrite proof_irrelevance with (z0 <> x0) n'1 n3... *)
    (**)
    (* dependent rewrite H2. *)
  Abort.


  Lemma answer_to_term_injective :
    forall {k} (a a' : answer k),
    answer_to_term a = answer_to_term a' -> a = a'.
  Proof with auto.
    destruct a; dependent destruction  a'; intros...
    f_equal; elim lCtx_plug_val_injective with l l0 v v0...
    elim lCtx_plug_needy with l lEmpty v _ n...
    elim lCtx_plug_needy with l lEmpty v _ n...
    inversion H.
    elim needy_to_term_injective with n n0; intros; subst...
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
    f_equal; elim ansCtx_plug_val_injective with a a0 (vLam v t) (vLam v0 t0); intros; subst...
    elim ansCtx_plug_val_injective with a a0 v v0; intros; subst...
    elim needy_to_term_injective with n n0; intros; subst...
  Qed.


  (* Here comes the actual definition of the grammar of contexts. *)
  (* We have two three non-trivial productions:  E -> E t,  E -> let x = t in E and *)
  (* E -> let x := E in E[x] *)
  (* There is also a trivial production  E -> [] which is omitted here. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *)


  Inductive eck : ckind -> ckind -> Type :=
  | ap_r  : term -> eck E E                           (* E -> E t *)
  | in_let : var -> term -> eck E E                   (* E -> let x = t in E *)
  | let_var : forall x, needy x -> eck E E.           (* E -> let x := E in E[x] *)

  Definition elem_context_kinded : ckind -> ckind -> Type := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  E.

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | ap_r  t' => App t t'
      | in_let x s => Let x s t
      | let_var x n => LetS x t n
      end.


  (* Here we define substitution used in the definition of contraction. *)

  (* substitute term s for the needed variable x in the needy term n *)
  Fixpoint subst_needy (x:var) (n:needy x) (s : term) : term :=
    match n with
    | nVar y => s           (* [x][x:=s] = s *)    (* types guarantee that x=y *)
    | nApp v n t => App (subst_needy v n s) t      (* (n[x] t)[x:=s] = (n[s] t) *)
                                                   (*  again, types guarantee that v=x *)
    | nLet y x' _ e n => Let y e (subst_needy x' n s)
                            (* (let y = e in n[x])[x:=s] =  (let y = e in n[s])*)
                            (* again, types guarantee that x=x' *)
    | nLetS y x' n n' => LetS y (subst_needy x' n s) n'
                              (* (let y := n[x] in n'[y])[x:=s] = (let y := n[s] in n'[y]) *)
                              (* here types guarantee that x=x' *)
    end.


  (* Now we are ready to define the contraction. *)
  (* For the sake of simplicity we do not introduce the fourth (derived) rule *)

  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp (vLam x r) a t => Some (ansCtx_plug a (Let x t r))    (* a[λx.r]t -> a[let x = t in r] *)
      | rLetS x n v a => Some (ansCtx_plug a (Let x (val_to_term v) (subst_needy x n v)))
                              (* let x := a[v] in n[x]  ->  a[let x = v in n[v]]  *)
      | rLet x t n => Some (LetS x t n)   (* let x = t in n  ->  let x := t in n  *)
      end.

  (* Having this we include some basic notions *)
  Include RED_SEM_BASE_Notions.

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
  Proof with auto.
    intros ? ? ec t v H.
    destruct ec;   dependent destruction v; inversion H;
    try (dependent destruction a;
    dependent destruction v; discriminate).
    destruct n; try discriminate.
    exists (ansNd x n); inversion H; subst...
    dependent destruction a; dependent destruction v; try discriminate.
    injection H1; intros; subst...
    exists (ansVal (vLam v t1) a)...
    destruct n; try discriminate.
    injection H; intros; subst;
    exists (ansNd _ n0); simpl; auto.
    destruct n0; try discriminate.
    inversion H1; subst...
    exists (ansNd _ n0_1)...
  Qed.


  (* A value is not a redex. *)

  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    intros k v r.
    destruct r; destruct v; intro H; inversion H;
    try (dependent destruction a0;
    dependent destruction v; try discriminate).
    destruct n; inversion H1; subst;
    elim ansCtx_plug_needy with a ansCtxEmpty v0 x n...
    destruct n0; try discriminate; inversion H; intros; subst.
    elim ansCtx_plug_needy with a ansCtxEmpty v0 _ n0_1...
    dependent destruction a;
    inversion H1; intros; subst...
    dependent destruction v; discriminate.
    elim ansCtx_plug_needy with a ansCtxEmpty v _ n...
    destruct n0; try discriminate.
    inversion H1; subst.
    elim needy_to_term_injective with n1 n...
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
    exists (ansVal v a)...
    exists (ansNd _ n)...
    exists (ansVal v a)...
  Qed.

End Lam_cbnd_PreRefSem.


(* The module type REF_STRATEGY is defined in the file *)
(*     refocusing/refocusing_semantics.v. *)
Module Lam_cbn_Strategy <: REF_STRATEGY Lam_cbnd_PreRefSem.

  Import Lam_cbnd_PreRefSem.
  Include RED_STRATEGY_STEP_Notions Lam_cbnd_PreRefSem.


  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)

  Definition dec_term t k : elem_dec k :=
    match k with E =>
                 match t with
                 | App t1 t2 => ed_dec  E t1 (ap_r t2)
                 | Var x     => ed_val (ansNd _ (nVar x))
                 | Lam x t1  => ed_val (ansVal (vLam x t1) ansCtxEmpty)
                 | Let x t1 t2 => ed_dec E t2 (in_let x t1)
                 | LetS x t n => ed_dec E t (let_var x n)
                 end
    end.

  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)

  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).
  Proof.
    destruct k,t ; simpl; auto.
  Qed.


  Definition dec_context {k k': ckind} (ec: elem_context_kinded k k') (v: value k') : elem_dec k :=
    match ec, v with
    | ap_r t, ansVal v' s => ed_red  (rApp v' s t)
    | ap_r t, ansNd _ n => ed_val (ansNd _ (nApp _ n t))
    | in_let x t, ansVal v' s => ed_val (ansVal v' (ansCtxLet x t s))
    | in_let x t, ansNd y n =>
      (match eq_var y x with
      | left peq => ed_red (rLet y t n) (* redex! *)
      | right pneq => ed_val (ansNd y (nLet x _ pneq t n))
      end)
    | let_var x n, ansVal v s => ed_red (rLetS _ n v s)
    | let_var x n, ansNd _ n' => ed_val (ansNd _ (nLetS x _ n' n))
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
    case_eq (eq_var x v0); intros; subst; auto.
  Qed.


  (* Here we define an order on elementary contexts but it is trivial in this case. *)
  Include Empty_search_order Lam_cbnd_PreRefSem.

  (* If two elementary contexts are prefixes of the same term, *)
  (* then they are equal. *)
  Lemma search_order_comp_if :         forall t k k' k'' (ec0 : elem_context_kinded k k')
                                                       (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0  ec1 [? ?] [? ?].
    do 2 right.
    subst t.
    destruct ec0; dependent destruction ec1;
    try discriminate;
    injection H0; intros; subst; auto.
    dependent destruction H.
    auto.
  Qed.


  (* Up-arrow function never returns that we should continue searching. *)
  Lemma dec_context_term_next :                        forall {k0 k1 k2} (v : value k1) t
                                                       (ec0 : elem_context_kinded k0 k1)
                                                       (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].

  Proof.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0; dependent destruction ec1; dependent destruction v;
    try discriminate;
    simpl in H; destruct (eq_var x v0); discriminate.
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


(* some terms for testing *)
Definition x  := Id 1.
Definition y  := Id 2.
Definition z  := Id 3.
Definition xx := λ x , # x @ # x.
Definition id := λ  x , # x.
Definition idz := λ  z , # z.
Definition t := xx @ idz.
Definition s := (λ x, ((λ y, # x @ # y) @ id)) @ id.
(* Example from Fig 2 in our paper on strong call by need *)
Definition fig2 :=  ((λ x, (λ y, # x @ # x)) @ (idz @ idz)) @ (Var (Id 4)).


Eval compute in list_configurations t 500.


(* and the complete machine *)
Print Lam_cbn_EAM.

