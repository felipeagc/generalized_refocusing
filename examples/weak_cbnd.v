(* Lambda calculus with the call-by-need reduction strategy *)
(* version of Danvy & Zerny PPDP13, 'revised cbneed λ_let-calculus of Fig. 5 *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.

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

  Inductive ck := E.
  Definition ckind := ck.
  Hint Unfold  ckind.


  (* Here we define the language of interest: lambda-let calculus.  *)
  (* Needys parameterized by a variable x are evaluation contexts *)
  (* with x plugged in the hole. Thus they are neutral terms with *)
  (* the variable x being needed. *)
  Inductive expr :=
  | App : expr -> expr -> expr                  (* application *)
  | Var : var -> expr                           (* variable *)
  | Lam : var -> expr -> expr                   (* lambda abstraction *)
  | Let : var -> expr -> expr -> expr           (* non-strict let *)
  | LetS : forall x, expr -> needy x -> expr (* strict let x := e in E[x] *)
  with
    needy : var -> Type := (* needys parameterized by head variable *)
  | nVar : forall x : var, needy x
  | nApp : forall x : var, needy x -> expr -> needy x       (* (n_x t) *)
  | nLet : forall y x, x <> y -> expr -> needy x -> needy x (* let y = e in n_x *)
  | nLetS : forall y x, needy x -> needy y -> needy x.      (* let y := n_x in n_y *)

Notation " t @ s " := (App t s) (at level 40).
Notation " # x " := (Var x) (at level 7).
Notation " t [ x / s ] " := (Let x s t) (at level 45).
Notation " 'λ'  x , t " := (Lam x t) (at level 50).


(* Answer contexts look like substitutions.  *)
Inductive ansCtx : ckind -> Type :=
  | ansCtxEmpty : ansCtx E
  | ansCtxLet : var -> expr -> ansCtx E -> ansCtx E.

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
  | ansVal : val E -> ansCtx E -> answer E (* (λ x . t) [y/s...] *)
  | ansNd : forall x, needy x -> answer E. (* all needys are open terms and (intermediate) answers *)

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
  Fixpoint ansCtx_plug {E} (s : ansCtx E) (t : term) :=
  match s with
  | ansCtxEmpty => t
  | ansCtxLet x r s' => Let x r (ansCtx_plug s' t)
  end.

  Fixpoint needy_to_term {x} (n : needy x) : term :=
  match n with
  | nVar x => Var x
  | nApp _ n t => App (needy_to_term n) t
  | nLet x y _ e n => Let x e (needy_to_term n)
  | nLetS y x n1 n2 => LetS y (needy_to_term n1) n2
  end.

  Fixpoint answer_to_term {k} (a : answer k) : term :=
  match a with
  | ansVal v s => ansCtx_plug s v
  | ansNd _ n   => needy_to_term n
  end.

  Coercion answer_to_term : answer >-> term.
  Coercion needy_to_term : needy >-> term.

  (* Here we define the set of potential redices. *)
  (* Actually, they are just redices as defined in the paper *)
  Inductive red : ckind -> Type :=
  | rApp : val E -> ansCtx E -> term -> red E                 (* A[v] t *)
  | rLetS : forall x, needy x -> val E -> ansCtx E -> red E   (* let x := A[v] in E[x] *)
  | rLet : forall x, term -> needy x -> red E.                (* let x = t in E[x] *)

  Definition redex := red.
  Hint Unfold redex.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp v s t => App (ansCtx_plug s v) t
      | rLetS x n v s => LetS x (ansCtx_plug s (val_to_term v)) n
      | rLet x t n => Let x t (needy_to_term n)
      end.

  Coercion redex_to_term : redex >-> term.

  (* This again is a required axiom in the signature of RED_SEM module *)
  Lemma val_to_term_injective :
      forall {k} (v v' : val k), val_to_term v = val_to_term v' -> v = v'.

  Proof with auto.
    destruct v. intros.
    dependent destruction v'.   inversion H. reflexivity.
  Qed.


  Lemma ansCtx_plug_val_injective :
    forall {k} (s s' : ansCtx k) (v v' : val E),
    ansCtx_plug s v = ansCtx_plug s' v' -> s = s' /\ v = v'.

  Proof with auto.
  intros k s s' v v' H.
  induction s; dependent destruction s'; inversion H.
  destruct v; dependent destruction v'; inversion H1...
  destruct v0; dependent destruction s'; inversion H1...
  dependent destruction s; destruct v'; inversion H1; split...
  split; f_equal; elim IHs with s'...
  Qed.



  Lemma ansCtx_plug_var_injective :
    forall {k} (s s' : ansCtx k) x x',
    ansCtx_plug s (Var x) = ansCtx_plug s' (Var x') -> s = s' /\ x = x'.

  Proof with auto.
  intros k s s' x x' H.
  induction s; dependent destruction s'; inversion H...
  elim IHs with s'; intros; subst...
 Qed.


  Lemma ansCtx_plug_lets_injective :
    forall {k} (s s' : ansCtx k) x y e1 e2 nx ny,
      ansCtx_plug s (LetS x e1 nx) = ansCtx_plug s' (LetS y e2 ny) ->
         s = s' /\ e1 = e2 /\ x = y /\ nx ~= ny.

  Proof with auto.
  intros k s s' x y e1 e2 nx ny H.
  induction s; dependent destruction s'; inversion H...
  elim IHs with s'; intros; subst...
 Qed.


  Lemma ansCtx_plug_needy :
    forall {k} (s s' : ansCtx k) (v : val E) {x} (n : needy x),
    ansCtx_plug s v = ansCtx_plug s' n -> False.

  Proof with auto.
  induction s; simpl; intros.
  destruct v; destruct s'; destruct n; discriminate.
  destruct s'. destruct n; simpl in *; try discriminate.
  inversion H. elim IHs with ansCtxEmpty v0 x n0...
  inversion H. elim (IHs _ _ _ _ H3).
  Qed.

  Lemma ansCtx_plug_var :
    forall {k} (s s' : ansCtx k) x (v : val E),
    ansCtx_plug s v = ansCtx_plug s' (Var x) -> False.

  Proof with auto.
  induction s; simpl; intros.
  destruct v; destruct s'; discriminate.
  destruct s'. discriminate.
  inversion H. elim IHs with s' x v0...
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
    subst; dependent rewrite H3.    elim IHn1 with n'1; intros; subst...
    dependent rewrite H0; auto.
    elim IHn1 with n'1...
  Qed.

  Lemma answer_to_term_injective :
    forall {k} (a a' : answer k),
    answer_to_term a = answer_to_term a' -> a = a'.

  Proof with auto.
    destruct a; dependent destruction  a'; intros...
    f_equal; elim ansCtx_plug_val_injective with a a0 v v0...
    elim ansCtx_plug_needy with a ansCtxEmpty v _ n...
    elim ansCtx_plug_needy with a ansCtxEmpty v _ n...
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


  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)

  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  (* In the case of weak call-by-need the order is trivial. *)
  (* We have three productions in the grammar; none of them are overlapping. *)
  (* So there is  nothing to compare. *)
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
    case_eq (eq_var x v0); intros; subst; rewrite H0 in H; discriminate].
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


