(* Lambda calculus with the strong call-by-need reduction strategy *)
(* Compiles with Coq v.8.7.2 *)
(* mabi 24.07.2018 *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.


Require Import List.
Require Import Eqdep.
Require Import ListSet.
Require Import Sets.


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

  
  (* set of variables *)  
  Definition vars := set var.


  (* E - weak cbnd, C - under lambda *)
  Inductive ck := E | C.

  (* kind is type paired with set of vars *)
  (* sets are modeled as lists with no duplication *)

  Inductive ckvars : Type :=
  | ckv : ck -> forall (xs : vars), NoDup xs -> ckvars.

  Definition ckind := ckvars.
  Hint Unfold  ckind.

  (* generate fresh name wrt given set of names *)
  Definition fresh_for (xs : vars) : var :=
    Id (1 + fold_right plus 0 (map (fun y => match y with Id x => x end) xs)).

  (* this is provable for our representation of vars *)
  Axiom fresh_for_is_fresh :
    forall x xs, fresh_for xs = x -> ~ In x xs.

  Notation " xs +++ ys " := (set_union eq_var xs ys) (right associativity, at level 60).
  Notation " x ::: xs " := (set_add eq_var x xs) (at level 60, right associativity).
  
  Hint Resolve set_union_intro1 set_union_intro2.

  Notation " ⋄ " := (empty_set var).
  
  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr
  | Let : var -> expr -> expr -> expr
  | LetNd : var -> expr -> expr -> expr.
                                  
  Inductive (* term that is decomposed as active variable in context *)
  in_ctx : ck -> var -> vars -> Type :=
  | inctxVar : forall {k} x, in_ctx k x ⋄
  | inctxApp_l : forall {k} x xs, ~ In x xs -> in_ctx E x xs -> expr -> in_ctx k x xs 
  | inctxApp_r : forall {k} x xs ys, ~ In x (xs ++ ys) -> struct ys ->
                              in_ctx C x xs -> in_ctx k x (ys +++ xs)
  | inctxLam : forall x y xs, x <> y -> in_ctx C y xs ->
                       in_ctx C y (set_remove eq_var x xs)
  | inctxSub : forall {k} x y xs, x <> y -> ~In x xs -> in_ctx k y xs -> expr ->
                           in_ctx k y xs  (* let x = e in [] *)
  | inctxNdSub : forall {k} x y xs zs, x <> y -> ~ In y xs -> struct xs ->
                                in_ctx k y zs ->
                                in_ctx k y (xs +++ (set_remove eq_var x zs)) (* let x :=s in []_x *)
  | inctxNdSub2 : forall {k} y xs, var -> in_ctx E y xs -> expr -> in_ctx k y xs

  with   (* structures parameterized by minimal set of frozen variables *)
  struct : vars -> Type :=
  | sVar : forall x, struct (x ::: ⋄)
  | sApp : forall xs ys, struct xs -> normal ys -> struct (xs +++ ys)
  | sSub : forall x ys, ~ In x ys -> expr -> struct ys ->
                   struct ys (* let x = e in s_ys *)
  | sNdSub : forall x ys zs xs, in_split x ys xs -> NoDup ys -> ~ In x ys ->
                           struct zs -> struct xs ->
                           struct (zs +++ ys) (* let x:= s_ys in s_xys *)

  with (* normal forms starting with lambda *)
  lambda_normal : vars -> Type :=
  | lnfLam : forall (x:var) xs, normal xs -> lambda_normal (set_remove eq_var x xs)
  | lnfSub : forall x ys, ~ In x ys -> expr -> lambda_normal ys -> lambda_normal ys (* let x = e in nf_ys *)
  | lnfNdSub : forall x ys zs xs, in_split x ys xs -> NoDup ys -> ~ In x ys ->
                             struct zs -> lambda_normal xs ->
                             lambda_normal (zs +++ ys) (* let x:= n_ys in nf_xys *)

  with (* normal forms parameterized by minimal set of frozen variables *)	      
  normal : vars -> Type :=
  | nf_struct : forall xs, struct xs -> normal xs
  | nf_lam_in_ctx : forall xs, lambda_normal xs -> normal xs. 


  Scheme struct_Ind   := Induction for struct Sort Prop
    with normal_Ind := Induction for normal Sort Prop
    with lambda_normal_Ind := Induction for lambda_normal Sort Prop.

  Scheme struct2_Ind   := Induction for struct Sort Prop
    with normal2_Ind := Induction for normal Sort Prop
    with lambda_normal2_Ind := Induction for lambda_normal Sort Prop
    with in_ctx_Ind := Induction for in_ctx Sort Prop.


  Notation " t @ s " := (App t s) (at level 40).
  Notation " # x " := (Var x) (at level 7).
  Notation " t [ x / s ] " := (Let x s t) (at level 45).
  Notation " 'lambda'  x , t " := (Lam x t) (at level 50, x ident).

  (* notation for explicit substitution with simple let *)
  Inductive sub (*{xs : vars} : ckind ->*) : Type :=
  | subMt : sub 
  | subCons : var -> expr -> sub -> sub.

  (* notation for explicit substitution with two kinds of lets*)
  Inductive sub_ext (*{xs : vars} : ckind ->*) : Type :=
  | subSimple : sub -> sub_ext 
  | subNd : var -> expr -> sub_ext -> sub_ext.
  
  
  Definition term := expr.
  Hint Unfold term.

  (* in terms E[x]ˢ x is not in frozen variables s *)
  Lemma inctx_var_notin_frozen :
    forall {k} x xs, @in_ctx k x xs -> ~ In x xs.
  Proof.
    induction 1;
      intro H; try elim H; auto.
    +
      elim n.
      apply in_or_app.
      elim (set_union_elim _ _  _ _ H); intros; right; auto.
      elim n; eauto.
    +
      elim IHX.
      eapply set_remove_1; eauto.
    +
      elim IHX.
      elim (set_union_elim _ _ _  _ H); intros; auto.
      elim n0; auto.
      eapply set_remove_1.
      eauto.
  Qed.

  Hint Resolve inctx_var_notin_frozen.

  Fixpoint sub_to_term (s : sub) (t : term) := 
    match s with
    | subMt => t
    | subCons x r s' => Let x r (sub_to_term s' t)
    end.
  
  Fixpoint sub_ext_to_term (s : sub_ext) (t : term) := 
    match s with
    | subSimple s => sub_to_term s t
    | subNd x r s => LetNd x r (sub_ext_to_term s t)
    end.
  
  Fixpoint struct_to_term {xs} (s : struct xs) : term := 
    match s with
    | sVar x => Var x
    | sApp xs ys s n => App (struct_to_term s) (normal_to_term n)
    | sSub x ys _ e s => Let x e (struct_to_term s)
    | sNdSub x ys _ _ _ _ _ s sx => LetNd x (struct_to_term s) (struct_to_term sx)
    end
      
  with
  lambda_normal_to_term {xs} ( n : lambda_normal xs) : term :=
    match n with
    | lnfLam x xs n => Lam x (normal_to_term n) 
    | lnfSub x ys _ e n => Let x e (lambda_normal_to_term n)
    | lnfNdSub x ys _ _ _ _ _ s n => LetNd x (struct_to_term s) (lambda_normal_to_term n)
    end
  with
  normal_to_term {xs} (n : normal xs) : term :=
    match n with
    | nf_struct _ s => struct_to_term s
    | nf_lam_in_ctx _ ln => lambda_normal_to_term ln
    end.
  
  Fixpoint
    nf_to_term {k} {x} {xs} ( neu : in_ctx k x xs) {struct neu}: term :=
    match neu with
    | inctxVar x => Var x
    | inctxApp_l x xs _ n e => App (nf_to_term n) e 
    | inctxApp_r x xs ys _ s neu' => App (struct_to_term s) (nf_to_term neu')
    | inctxLam x y xs  _ neu' => Lam x (nf_to_term neu') 
    | inctxSub x y xs _ _ n e => Let x e (nf_to_term n) 
    | inctxNdSub x y xs _  _ _ s n => LetNd x (struct_to_term s) (nf_to_term n)
    | inctxNdSub2 y xs x ny nx => LetNd x (nf_to_term ny) nx
    end.
  
  Definition struct_to_normal {xs} (s : struct xs) : normal xs := nf_struct xs s.

  Coercion struct_to_normal : struct >-> normal.
  Coercion normal_to_term : normal >-> term.
  Coercion nf_to_term : in_ctx >-> term.
  Coercion struct_to_term : struct >-> term.

  (* values *)
  Inductive val : ckind -> Type :=
  | vCLam : forall {xs} ys (Hnd : NoDup ys),  Subset xs ys -> lambda_normal xs ->
                                         val (ckv C ys Hnd)
  | vStruct : forall {k} {xs} ys (Hnd : NoDup ys), Subset xs ys -> struct xs ->
                                              val (ckv k ys Hnd)
  | vNeu : forall {k} {xs} x ys (Hnd : NoDup ys), ~In x ys -> Subset xs ys ->
                                             in_ctx k x xs -> val (ckv k ys Hnd)
  | vELam : forall xs (Hnd : NoDup xs), var -> term -> sub -> val (ckv E xs Hnd).

  
  Definition value := val.
  Hint Unfold value.

  Fixpoint val_to_term {k} (v : val k) : term :=
    match v with
    | vCLam ys _ _ n => lambda_normal_to_term n
    | vStruct xs _ _ s => struct_to_term s
    | vNeu xs _ x  _ _  n => nf_to_term n
    | vELam _ _ x t s => sub_to_term s (Lam x t)
    end.  

  Coercion val_to_term : val >-> term.
  Definition value_to_term {k} := @val_to_term k.


  (* Here we define the set of potential redices. *)
  
  Inductive red : ckind -> Type :=
  | rApp : forall {k} {xs} {Hnd : NoDup xs},
      var -> term -> sub -> term -> red (ckv k xs Hnd)
  | rSub : forall {k} (x: var) xs {Hnd : NoDup xs},
      expr -> var -> term -> sub -> red (ckv k xs Hnd)
  | rSubNd : forall {k} x xs ys {Hnd : NoDup ys},
      Subset xs ys -> in_ctx k x xs -> term -> red (ckv k ys Hnd)
  | rSubWrong : forall {k} x xs ys zs {Hnd : NoDup ys},
      Subset xs ys -> Subset zs ys -> ~ In x zs -> struct xs -> struct zs -> red (ckv k ys Hnd)
  | rSubWrong2 : forall x xs ys zs {Hnd : NoDup ys},
      Subset xs ys -> Subset zs ys -> ~ In x zs -> struct xs -> lambda_normal zs -> red (ckv C ys Hnd)
  | rSubNdE : forall (x : var) xs ys {Hnd : NoDup ys},
      Subset xs ys -> struct xs -> var -> term -> sub -> red (ckv E ys Hnd).

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

  
  Definition redex_to_term {k} (r : redex k) : term :=
    match r with
    | rApp x t s t' => App (sub_to_term s (Lam x t)) t'
    | rSub  x _ n y t s => LetNd x (sub_to_term s (Lam y t)) (n:term)
    | rSubNd x xs _  _ n t => Let x t (n:term)
    | rSubWrong x xs _ _ _ _ _ s s1 => LetNd x (s:term) (s1:term)
    | rSubWrong2 x xs _ _ _ _ _ s s1 => LetNd x (s:term) (lambda_normal_to_term s1)
    | rSubNdE x xs _ _  s y t s0 => LetNd x (s : term) (sub_to_term s0 (Lam y t))
    end.
  
  Coercion redex_to_term : redex >-> term.

  (* struct cannot begin with lambda *)
  Lemma struct_not_sub_lambda :
    forall xs (s: struct xs)  t, struct_to_term s = t ->
                            forall v s0 r, t = sub_to_term s0 (Lam v r) ->   False.
  Proof.
    induction s; destruct t; destruct s0; try discriminate; auto.
    intros; inversion H0; inversion H; subst; auto.
    eelim IHs; eauto.
  Qed.

  Hint Resolve struct_not_sub_lambda.

  (* struct cannot be normal form beginning with lambda *)
  Lemma struct_not_lambda :
    forall xs (s: struct xs) ys (l:lambda_normal ys),
      struct_to_term s = lambda_normal_to_term l -> False.
  Proof.
    induction s; destruct l; intros; try inversion H; subst; auto.
    eapply IHs; eauto.
    eapply IHs2; eauto.
  Qed.

  Hint Resolve struct_not_lambda.  

  (* variable in context cannot begin with lambda *)
  Lemma inctx_E_not_sub_lambda :
    forall k x xs (s: in_ctx k x xs)  t,
      nf_to_term s = t -> forall v s0 r, t = sub_to_term s0 (Lam v r) -> k = E ->  False.
  Proof with eauto.
    induction s; destruct t; intros; inversion H; subst;
      try (inversion H0; dependent destruction s0; try discriminate);
      try (destruct s1; discriminate)...
    injection H0; intros...
  Qed.
  
  Hint Resolve inctx_E_not_sub_lambda.
  
  Lemma struct_to_term_injective : 
    forall {xs} (n : struct xs) {ys} (n' : struct ys), 
      struct_to_term n = struct_to_term n' -> n ~= n' /\ xs = ys. 
  Proof with eauto.
    induction n using struct_Ind with
        (P:= fun xs n =>  forall ys (n' : struct ys), 
                 struct_to_term n = struct_to_term n' -> n ~= n' /\ xs = ys)
        (P1:= fun xs n => forall ys (n' : lambda_normal ys), 
                  lambda_normal_to_term n = lambda_normal_to_term n' -> n ~= n' /\ xs = ys)
        (P0:= fun xs n => forall ys (n' : normal ys), 
                  normal_to_term n = normal_to_term n' -> n ~= n' /\ xs = ys);
      intros;  
      destruct n'; try discriminate; inversion H; subst;  
        try elim IHn with _ n'; try elim IHn0 with _ n1; try eelim IHn1; try eelim IHn2; intros; eauto;  split; dep_subst; eauto.
    +
      rewrite proof_irrelevance with (p1:=n) (p2:=n1)...

    +
      assert (hh:=in_split_inv _ _ _ _ i i0); subst...
      rewrite proof_irrelevance with _ i  i0...
      rewrite proof_irrelevance with _ n2  n0...
      rewrite proof_irrelevance with _ n  n1...
    +
      assert (hh:=in_split_inv _ _ _ _ i i0); subst...
    +
      elim IHn with xs0 s; intros;
      subst...
      subst...
    +
      eapply IHn; eauto.
    +
      eelim struct_not_lambda...
    +
      eelim struct_not_lambda...
    +
      eelim struct_not_lambda...
    +
      eelim struct_not_lambda...
    +
      eelim IHn; intros; subst...
      subst xs.
      rewrite H0...
    +
      eelim IHn; intros ; subst...
    +
      eelim IHn; intros ; subst...
      subst; rewrite H0...
    +
      elim IHn with _ n0; intros; subst...
    +
      rewrite proof_irrelevance with _ n  n0...
    +
      elim IHn with _ s; intros; subst...
      elim IHn0 with _ n'; intros; subst...
      assert (hh:=in_split_inv _ _ _ _ i i0).
      subst...
      rewrite proof_irrelevance with _ n  n2...
      rewrite proof_irrelevance with _ n0  n3...
      rewrite proof_irrelevance with _ i i0...
    +
      elim IHn with _ s; intros; subst...
      elim IHn0 with _ n'; intros; subst...
      assert (hh:=in_split_inv _ _ _ _ i i0).
      subst...      
  Qed.
  
  Hint Resolve struct_to_term_injective.
  
  Ltac ind_proof :=
    match goal with
    | [ IHn : forall _ _, _ = _ -> _ /\ _  |- _ ] => eelim IHn; intros; subst; eauto; clear IHn; ind_proof
    | [ H : _ = _ |- _ ] => progress subst; clear H; ind_proof
    | [ H : _ :: _ = _ |- _ ] => inversion H; intros; subst; clear H; ind_proof 
    | [ H : _ ~= _ |- _ ] => rewrite H; clear H; ind_proof
    | [ H : ~ In _ _ ,  H1 : ~ In _ _ |- _ ] => rewrite proof_irrelevance with _ H H1; trivial; clear H; ind_proof
    | [ |- _ /\ _ ] => split; eauto
    end.

  Lemma lambda_normal_to_term_injective :   
    forall {xs} (n : lambda_normal xs) {ys} (n' : lambda_normal ys), 
      lambda_normal_to_term n = lambda_normal_to_term n' -> n ~= n' /\ xs = ys.
  Proof with eauto.
    induction n using lambda_normal_Ind with
        (P:= fun xs n =>
               forall ys (n' : struct ys), 
                 struct_to_term n = struct_to_term n' -> n ~= n' /\ xs = ys)
        (P1:= fun xs n => forall ys (n' : lambda_normal ys), 
                  lambda_normal_to_term n = lambda_normal_to_term n' -> n ~= n' /\ xs = ys)
        (P0:= fun xs n => forall ys (n' : normal ys), 
                  normal_to_term n = normal_to_term n' -> n ~= n' /\ xs = ys); intros;  
      destruct n'; try discriminate; inversion H; subst; trivial; eauto.
    + 
      elim (IHn _ _ H1); intros; subst...
      split...
      rewrite H0...
    +
      eelim struct_not_lambda...
    +
      eelim struct_not_lambda...
    +
      elim (IHn _ _ H1); intros; subst...
      split...
      rewrite H0...
    +
      elim (IHn _ _ H2); intros; subst...
      split...
      rewrite H0...
    +
      elim (IHn _ _ H3); intros; subst.
      rewrite H0.
      split...
      rewrite proof_irrelevance with _ n n1...
    +
      elim (IHn _ _ H2); intros; subst.
      elim (IHn0 _ _ H3); intros; subst.
      assert (hg:=in_split_inv _ _ _ _ i i0).
      subst...
      split...
      rewrite proof_irrelevance with _ n n2...
      rewrite proof_irrelevance with _ n0 n3...
      rewrite proof_irrelevance with _ i i0...
  Qed.

  Lemma normal_to_term_injective :   
    forall {xs} (n : normal xs) {ys} (n' : normal ys), 
      normal_to_term n = normal_to_term n' -> n ~= n' /\ xs = ys.
  Proof with eauto.
    induction n using normal_Ind with
        (P:= fun xs n =>
               forall ys (n' : struct ys), 
                 struct_to_term n = struct_to_term n' -> n ~= n' /\ xs = ys)
        (P1:= fun xs n => forall ys (n' : lambda_normal ys), 
                  lambda_normal_to_term n = lambda_normal_to_term n' -> n ~= n' /\ xs = ys)
        (P0:= fun xs n => forall ys (n' : normal ys), 
                  normal_to_term n = normal_to_term n' -> n ~= n' /\ xs = ys); intros;  
      destruct n'; try discriminate; inversion H; subst; trivial; eauto.
    + 
      elim (IHn _ _ H1); intros; subst...
      split...
      rewrite H0...
    +
      eelim struct_not_lambda...
    +
      eelim struct_not_lambda...
    +
      elim (IHn _ _ H1); intros; subst...
      split...
      rewrite H0...
    +
      elim (IHn _ _ H2); intros; subst...
      split...
      rewrite H0...
    +
      elim (IHn _ _ H3); intros; subst.
      rewrite H0.
      split...
      rewrite proof_irrelevance with _ n n0...
    +
      elim (IHn _ _ H2); intros; subst.
      elim (IHn0 _ _ H3); intros; subst.
      assert (hg:=in_split_inv _ _ _ _ i i0).
      subst...
      split...
      rewrite proof_irrelevance with _ n n1...
      rewrite proof_irrelevance with _ n0 n2...
      rewrite proof_irrelevance with _ i i0...
  Qed.

  Lemma struct_NoDup : 
    forall {xs} (n : struct xs), 
      NoDup xs. 
  Proof with eauto.
    induction 1 using struct_Ind with
        (P:= fun xs n => NoDup xs)
        (P1:= fun xs n =>     NoDup xs)
        (P0:= fun xs n =>     NoDup xs); intros; try repeat constructor...
  Qed.
  
  Lemma lambda_normal_NoDup : 
    forall {xs} (n : lambda_normal xs), 
      NoDup xs. 
  Proof with eauto.
    induction 1 using lambda_normal_Ind with (P:= fun xs n => NoDup xs)
                                        (P1:= fun xs n =>     NoDup xs)
                                        (P0:= fun xs n =>     NoDup xs); intros...
    repeat constructor...
  Qed.
  
  Lemma normal_NoDup : 
    forall {xs} (n : normal xs), 
      NoDup xs. 
  Proof with eauto.
    induction 1 using normal_Ind with (P:= fun xs n => NoDup xs)
                                      (P1:= fun xs n =>     NoDup xs)
                                      (P0:= fun xs n =>     NoDup xs); intros...
    repeat constructor...
  Qed.
  
  Lemma neutral_NoDup : 
    forall {k} {x} {xs} (n : in_ctx k x xs), 
      NoDup xs. 
  Proof with eauto.
    induction 1 using in_ctx_Ind with (P:= fun xs n => NoDup xs)
                                      (P1:= fun xs n =>     NoDup xs)
                                      (P0:= fun xs n =>     NoDup xs); intros...
    repeat constructor...
    constructor.
  Qed.
  
  Hint Resolve struct_NoDup lambda_normal_NoDup normal_NoDup neutral_NoDup.
  
  (* if E[x]^ys = s ^xs then x is in xs *)
  Lemma normal_vars_neutral :
    forall xs (s: normal xs) k x ys (n : in_ctx k x ys), 
      normal_to_term s = nf_to_term n -> In x xs.
  Proof with eauto.
    induction s using normal_Ind with
        (P:= fun xs s => forall k x ys (n:in_ctx k x ys),
                 struct_to_term s = nf_to_term n -> In x xs)
        (P0:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  normal_to_term s = nf_to_term n -> In x xs) 
        (P1:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  lambda_normal_to_term s = nf_to_term n -> In x xs) 
    ; simpl; intros; subst;
      match goal with
      | [ n : in_ctx _ _ _ |- _ ] => dependent destruction n
      | _ => idtac
      end; try discriminate... 
    +
      inversion H; subst...
    +
      injection H; intros; subst...
      apply set_union_intro1; eapply IHs...
    +
      injection H; intros; subst...
      apply set_union_intro2; eapply IHs0...
    +
      injection H; intros; subst...
    +
      injection H; intros; subst...
      elim struct_to_term_injective with s _ s1; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      assert (hh:=IHs0 _ _ _ _ H0)...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H2; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app; auto.
      auto.
    +

      injection H; intros; subst...
      apply set_union_intro1; eapply IHs...
    +
      inversion H; subst...
      apply set_remove_3...
    +   
      inversion H; subst...
    +
      inversion H; subst...
      assert (hh:=IHs0 _ _ _ _ H3)...
      elim struct_to_term_injective with s _ s0; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H0; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app...
      auto.
    +
      inversion H; subst...
      assert (hh:=IHs _ _ _ _ H2)...
      apply set_union_intro1...
      
      
  Qed.
  
  Hint Resolve normal_vars_neutral.  

  (* if E[x]^ys = s ^ xs then x is in xs *)
  Lemma lambda_normal_vars_neutral :
    forall xs (s: lambda_normal xs) k x ys (n : in_ctx k x ys), 
      lambda_normal_to_term s = nf_to_term n -> In x xs.
  Proof with eauto.
    induction s using lambda_normal_Ind with
        (P:= fun xs s => forall k x ys (n:in_ctx k x ys),
                 struct_to_term s = nf_to_term n -> In x xs)
        (P0:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  normal_to_term s = nf_to_term n -> In x xs) 
        (P1:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  lambda_normal_to_term s = nf_to_term n -> In x xs) 
    ; simpl; intros; subst;
      match goal with
      | [ n : in_ctx _ _ _ |- _ ] => dependent destruction n
      | _ => idtac
      end; try discriminate... 
    +
      inversion H; subst...
    +
      injection H; intros; subst...
      apply set_union_intro1; eapply IHs...
    +
      injection H; intros; subst...
      apply set_union_intro2; eapply IHs0...
    +
      injection H; intros; subst...
    +
      injection H; intros; subst...
      elim struct_to_term_injective with s _ s1; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      assert (hh:=IHs0 _ _ _ _ H0)...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H2; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app; auto.
      auto.
    +

      injection H; intros; subst...
      apply set_union_intro1; eapply IHs...
    +
      inversion H; subst...
      apply set_remove_3...
    +   
      inversion H; subst...
    +
      inversion H; subst...
      assert (hh:=IHs0 _ _ _ _ H3)...
      elim struct_to_term_injective with s _ s1; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H0; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app...
      auto.
    +
      inversion H; subst...
      assert (hh:=IHs _ _ _ _ H2)...
      apply set_union_intro1...
  Qed.      

  
  Hint Resolve lambda_normal_vars_neutral.  
  
  Lemma struct_vars_neutral :
    forall xs (s: struct xs) k x ys (n : in_ctx k x ys), 
      struct_to_term s = nf_to_term n -> In x xs.
  Proof with eauto.
    induction s using struct_Ind with
        (P:= fun xs s => forall k x ys (n:in_ctx k x ys),
                 struct_to_term s = nf_to_term n -> In x xs)
        (P0:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  normal_to_term s = nf_to_term n -> In x xs) 
        (P1:= fun xs s => forall k x ys (n:in_ctx k x ys),
                  lambda_normal_to_term s = nf_to_term n -> In x xs) 
    ; simpl; intros; subst;
      match goal with
      | [ n : in_ctx _ _ _ |- _ ] => dependent destruction n
      | _ => idtac
      end; try discriminate... 
    +
      inversion H; subst...
    +
      injection H; intros; subst...
      apply set_union_intro1; eapply IHs...
    +
      injection H; intros; subst...
      apply set_union_intro2; eapply IHs0...
    +
      injection H; intros; subst...
    +
      injection H; intros; subst...
      elim struct_to_term_injective with s _ s1; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      assert (hh:=IHs2 _ _ _ _ H0)...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H2; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app; auto.
      auto.
    +

      injection H; intros; subst...
      apply set_union_intro1; eapply IHs1...
    +
      inversion H; subst...
      apply set_remove_3...
    +   
      inversion H; subst...
    +
      inversion H; subst...
      assert (hh:=IHs0 _ _ _ _ H3)...
      elim struct_to_term_injective with s _ s0; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4]]]; subst...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H0; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app...
      auto.
    +
      inversion H; subst...
      assert (hh:=IHs _ _ _ _ H2)...
      apply set_union_intro1...
  Qed.      



  Hint Resolve struct_vars_neutral.

  Ltac ind_proof2 :=
    match goal with
    | [ IHn : forall _ _, ?tm = _ -> _ , Heq : ?tm = _  |- _ ] => assert (hh:=IHn _ _ Heq); auto; clear IHn; ind_proof2
    | [ IHn : forall _ _ _, ?tm = _ -> _ , Heq : ?tm = _  |- _ ] => elim (IHn _ _ _ Heq); intros; subst; auto; clear IHn; ind_proof2
    | [ H : _ :: _ = _ |- _ ] => inversion H; intros; subst; clear H; ind_proof2 
    | [ H : _ = _ |- _ ] => subst; clear H; ind_proof2
    | [ H : _ ~= _ |- _ ] => rewrite H; clear H; ind_proof2
    | [ H : _ /\ _ |- _ ] => destruct H; ind_proof2
    | [ H : ~ In _ _ ,  H1 : ~ In _ _ |- _ ] => rewrite proof_irrelevance with _ H H1; trivial; clear H;  ind_proof2
    | [ H : struct_to_term _ = lambda_normal_to_term _ |- _ ] => eelim struct_not_lambda; eauto
    | [ |- _ /\ _ ] => split; eauto
    end.


  Lemma neutral_to_term_vars : 
    forall {k} {x} {xs} (n : in_ctx k x xs) y ys (n' : in_ctx k y ys), 
      nf_to_term n = nf_to_term n' -> x <> y -> In x ys \/ In y xs.
  Proof with eauto.
    induction n; intros;
      dependent destruction n'; try discriminate; inversion H; subst...
    +
      elim H0...
    +
      assert (hh:=struct_vars_neutral  _ _ _ _ _ _ (eq_sym H2)).
      left.
      apply set_union_intro1...
    +
      assert (hh:=struct_vars_neutral  _ _ _ _ _ _ H2).
      right.
      apply set_union_intro1...
    +
      elim struct_to_term_injective with s _ s0; intros; subst...
      elim (IHn _ _ _ H3); intros...
      left.
      apply set_union_intro; right...
      right. 
      apply set_union_intro; right...
    +
      assert (hh:=IHn _ _ _ H3 H0)...
      destruct hh.
      left.
      apply set_remove_3...
      right.
      apply set_remove_3...
    +
      elim struct_to_term_injective with s _ s0; intros; subst...
      elim (IHn _ _ _ H4); intros...
      left.
      apply set_union_intro; right...
      apply set_remove_3...
      right.
      apply set_union_intro; right...
      apply set_remove_3...
    +
      assert (hh:=struct_vars_neutral  _ _ _ _ _ _ H3).
      right.
      apply set_union_intro; left...
    +
      assert (hh:=struct_vars_neutral  _ _ _ _ _ _ (eq_sym H3)).
      left.
      apply set_union_intro; left...
  Qed.
  

  Lemma neutral_to_term_injective : 
    forall k x xs (n : in_ctx k x xs) ys (n' : in_ctx k x ys), 
      nf_to_term n = nf_to_term n' ->
      @eq_dep vars (fun xs => in_ctx k x xs) xs n ys n'.
  Proof with eauto.
    induction n; intros; dependent destruction n'; try discriminate; inversion H; subst...
    +
      assert (hh:=IHn _ _ H1).
      inversion hh; subst.
      rewrite proof_irrelevance with _ n n1...
      dependent destruction H4...
    +
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ (eq_sym H1)).
      elim n1...
    +
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ H1).
      elim n...
    +
      elim struct_to_term_injective with s _ s0; intros; subst.
      rewrite H0.
      destruct (IHn _ _ H2); subst...
      rewrite proof_irrelevance with _ n n1...
      auto.  
    +
      destruct (IHn _ _ H2); subst...
      rewrite proof_irrelevance with _ n n1...
    +
      destruct (IHn _ _ H3); subst...
      rewrite proof_irrelevance with _ n n2...
      rewrite proof_irrelevance with _ n0 n3...
    +
      elim struct_to_term_injective with s _ s0; intros; subst...
      rewrite H0.
      destruct (IHn _ _ H3); subst...
      rewrite proof_irrelevance with _ n n2...
      rewrite proof_irrelevance with _ n0 n3...
    +
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ H2).
      elim n0...
    +
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ (eq_sym H2)).
      elim n1...
    +
      destruct (IHn _ _ H2); subst...
      
  Qed.

  Lemma sub_to_term_val_injective : 
    forall (s s' : sub) x y t t', 
      sub_to_term s (Lam x t) = sub_to_term s' (Lam y t') ->
      s = s' /\ Lam x t = Lam y t'.
  Proof with eauto.
    intros s. 
    induction s; intros; dependent destruction s'; intros.
    inversion H; subst...
    inversion H; discriminate.
    inversion H; discriminate.
    inversion H; intros; subst.
    inversion H; intros; subst...
    elim IHs with s' x y t t'; intros; subst...
  Qed.  


  Lemma sub_to_term_var_injective : 
    forall (s s' : sub) x x', 
      sub_to_term s (Var x) = sub_to_term s' (Var x') -> s = s' /\ x = x'.
  Proof with eauto.
    intros s. 
    induction s; intros; dependent destruction s'; inversion H...
    elim IHs with s' x x'; intros; subst...
  Qed.


  Lemma value_to_term_injective : 
    forall {k} (a a' : value k), 
      value_to_term a = value_to_term a' -> a = a'.
  Proof with eauto.
    dependent destruction a; dependent destruction  a'; intros; inversion H;
      subst; rewrite (proof_irrelevance _ Hnd0 Hnd) in x;
        rewrite <- x in H1...
    +
      elim lambda_normal_to_term_injective with l _ l0; intros; subst...
      rewrite proof_irrelevance with _ s  s0...
      simpl in *.
      rewrite H0...
    +
      eelim struct_not_lambda...
    +
      assert (hh:=lambda_normal_vars_neutral _ l _ _ _ _ H1)...
      elim n...
    +
      eelim struct_not_lambda...
    +
      elim struct_to_term_injective with s0 _ s2; intros; subst ...
      rewrite H0.
      rewrite proof_irrelevance with _ s s1...
    +
      assert (hh:=struct_vars_neutral _ s0 _ _ _  i H1).
      elim subset_not_in with xs ys x0...
    +
      eelim struct_not_sub_lambda...
    +
      assert (hh:=lambda_normal_vars_neutral _ l _ _ _ _ (eq_sym H1))...
      elim n...
    +
      assert (hh:=struct_vars_neutral _ s1 _ _ _  i (eq_sym H1)).
      elim subset_not_in with xs0 ys x0...
    +
      case_eq (eq_var x1 x0); intros; subst...
      assert (h:=neutral_to_term_injective _ _ _ _ _ _ H1)...
      inversion h...
      subst...
      dependent destruction H5.
      rewrite proof_irrelevance with _ s  s0...
      rewrite proof_irrelevance with _ n  n0...
      eelim neutral_to_term_vars; intros; subst...
      elim n...
      elim n0...
    +
      eelim inctx_E_not_sub_lambda...
    +
      eelim struct_not_sub_lambda...
    +
      eelim inctx_E_not_sub_lambda...
    +
      eelim sub_to_term_val_injective; intros; subst...
      subst.
      inversion H2...
  Qed.
  

  Lemma redex_to_term_injective : 
    forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.
  Proof with eauto.
    intros k r r' H.
    dependent destruction r ; dependent destruction r';
      inversion H; subst; rewrite (proof_irrelevance _ Hnd0 Hnd) in * ;
        rewrite <-x in *; inversion H1; subst...
    +
      elim sub_to_term_val_injective with s s0 v v0 t t1; intros; subst...
      inversion H3; subst...
    +
      elim sub_to_term_val_injective with s s0 v v0 t t0; intros; subst...
      inversion H2; subst...
    +
      simpl in *.
      inversion H1; subst.
      eelim (struct_not_sub_lambda); eauto.
    +
      eelim struct_not_sub_lambda; eauto.
    +
      eelim struct_not_sub_lambda; eauto.
    +
      assert (hh:=neutral_to_term_injective _ _ _ i _ i0 H4).
      inversion hh.
      dependent destruction H5.
      rewrite proof_irrelevance with _ s s0.
      auto.
    +
      eelim struct_not_sub_lambda; eauto.
    +
      elim struct_to_term_injective with s1 _ s5; intros; eauto.
      elim struct_to_term_injective with s2 _ s6; intros; eauto.
      subst...
      rewrite proof_irrelevance with _ s s3...
      rewrite proof_irrelevance with _ s0 s4...
      rewrite proof_irrelevance with _ n n0...
      rewrite H0.
      rewrite H5...
    +
      eelim (struct_not_lambda); eauto.
    +  
      eelim (struct_not_sub_lambda); eauto.
    +
      eelim (struct_not_sub_lambda); eauto.
    +
      eelim (struct_not_lambda); eauto.
    +
      elim struct_to_term_injective with s1 _ s4; intros; eauto.
      elim lambda_normal_to_term_injective with l _ l0; intros; eauto.
      subst...
      rewrite proof_irrelevance with _ s s2...
      rewrite proof_irrelevance with _ s0 s3...
      rewrite proof_irrelevance with _ n n0...
      rewrite H0.
      rewrite H5...
    +
      eelim struct_not_sub_lambda with (s:=s0); eauto.
    + 
      eelim struct_not_sub_lambda with (s:=s5); eauto.
    +
      elim struct_to_term_injective with s0 _ s3; intros; eauto.
      subst...
      assert (hh:=sub_to_term_val_injective _ _ _ _ _ _ H4).
      destruct hh; subst...
      inversion H5; subst...
      rewrite proof_irrelevance with _ s s2...
  Qed.
  
  
  Lemma NoDup_cons :
    forall {xs : vars}, NoDup xs -> forall {x}, ~ In x xs -> NoDup (x::xs).
  Proof.
    induction 1; simpl; intros; eauto; constructor; try intro; eauto.
    constructor.
  Qed.
  
  Hint Resolve NoDup_cons.

  Inductive eck : ckind -> ckind -> Type := 
  | k_lam_c : forall {xs} x (Hnd : NoDup xs) (HIn : ~In x xs),  eck (ckv C xs Hnd) (ckv C (x::xs) (NoDup_cons Hnd HIn)) (* lam x. []_C *)
  | k_ap_r  : forall {xs} {k} (Hnd : NoDup xs), term -> eck (ckv k xs Hnd) (ckv E xs Hnd) (* []_E t *)
  | k_ap_l_E  : forall {k} xs ys (Hnd : NoDup xs), Subset ys xs -> struct ys -> eck (ckv k xs Hnd) (ckv C xs Hnd) (* s []_C *)
  (*  | k_ap_l_C  : forall xs, normal xs -> eck C C (* in_ctx []_C *)*)
  | in_let : forall {k} xs (x : var) (Hnd : NoDup xs), ~ In x xs -> term -> eck (ckv k xs Hnd) (ckv k xs Hnd) (* let x = t in []_k *)

  | let_var : forall {k} xs (x:var) (Hnd : NoDup xs), (*in_ctx k x ys ->*) expr -> eck (ckv k xs Hnd) (ckv E xs Hnd) (* let x:=[]_E in n *)
  | let_var2 : forall {k} x xs ys (Hnd : NoDup ys) (HIn : ~In x ys), Subset xs ys -> struct xs -> eck (ckv k ys Hnd) (ckv k (x::ys) (NoDup_cons Hnd HIn)).

  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.


  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  ckv C [] (NoDup_nil _).

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
    match ec with
    | k_lam_c x _ _ => Lam x t
    | k_ap_r _ tr => App t tr
    | k_ap_l_E x _ _ _ s  => App (s : term) t
    | in_let _ x _ _ s => Let x s t
    | let_var xs x _ s => LetNd x t (s:term) (*LetNd x xs t s*)
    | let_var2 x xs _ _ _ _ s => LetNd x (s : term) t
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
  Inductive context (k1 : ckind) : ckind -> Type :=
  | empty : context k1 k1
  | ccons : forall {k2 k3}
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
    | rApp x r s t => Some (sub_to_term s (Let x t r))
    | rSub  x xs n y t s => Some (subst x n (sub_to_term s (Lam y t))) 
    | rSubNd x xs _ _ n e => Some (LetNd x e (n:term))  
    | _ => None
    end.
  

  (* Decomposition of a term is a pair consisting of a reduction context and *)
  (* a potential redex. Values have no decomposition; we just report that *)
  (* the term is a value. *)
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
      preservation :
        forall t1 t2,
          P t1  ->   ltransition k t1 t2 ->  P t2;
      progress :
        forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2,                                          ltransition k t1 t2)
    }.


  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                        exists (v' : value k2), t = v'.
  Proof with eauto.
    intros ? ? ec t v H;
      dependent destruction ec;
      dependent destruction v; inversion H; subst;
        rewrite (proof_irrelevance _ Hnd0 Hnd) in *; rewrite <- x in *.
    destruct l; try discriminate; simpl in *.
    inversion H1; subst.
    assert (Subset xs0 (x1 :: xs)).
    unfold Subset in *; intros; eauto.
    case_eq (eq_var x x1); intros; subst...
    left; auto.
    right.
    apply s.
    eapply set_remove_3; eauto.
    dependent destruction n.
    exists (vStruct _ _ H0 s0)...
    exists (vCLam _ _ H0 l)...
    +
      destruct s0; discriminate.
    +
      dependent destruction i; try discriminate; inversion H1; subst...
      simpl in *.
      assert (Subset xs1 (x::xs)).
      unfold Subset in *; intros; subst...
      case_eq (eq_var x x0); intros; subst...
      left; auto.
      right; apply s.
      apply set_remove_3...
      assert (~In y (x::xs)).
      intro.
      destruct H2; subst...
      exists (vNeu _ _ _ H2 H0 i)...
    +
      destruct l; try discriminate; inversion H1; subst.
    +
      destruct s0; try discriminate; inversion H1; subst.
      simpl in *. 
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; subst...
      apply s.
      apply set_union_intro1...
      exists (vStruct _ _ H0 s0)...
    +
      dependent destruction i; try discriminate;
        inversion H1; subst.
      exists (vNeu _ _ _ n s i)...
      assert (Subset ys xs)...
      unfold Subset in *; intros; subst...
      apply s.
      apply set_union_intro1...
      exists (vStruct _ _ H0 s0)...
    +
      destruct s; discriminate.
    +
      destruct l; discriminate.
    +
      destruct s2; try discriminate; inversion H1; subst...
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      dependent destruction n; simpl in *.
      assert (Subset xs1 xs)...
      unfold Subset in *; intros; subst...
      apply s1.
      apply set_union_intro2...
      exists (vStruct _ _ H3 s3)...
      assert (Subset xs1 xs)...
      unfold Subset in *; intros; eauto.
      eapply s1; eauto.
      apply set_union_intro2...
      exists (vCLam _ _ H3 l)...
    +    
      dependent destruction i; try discriminate; inversion H1; subst...
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ H2).
      elim n...
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      simpl in *.
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; eauto.
      eapply s1; eauto.
      apply set_union_intro2...
      exists (vNeu _ _ _ n H3 i)...
    + 
      destruct s1; discriminate.
    +
      destruct l; try discriminate; inversion H1; subst...
      exists (vCLam _ _ s l)...
    +
      destruct s0; try discriminate; inversion H1; subst.
      exists (vStruct _ _ s s0)...
    +
      destruct i; try discriminate; inversion H1; subst...
      simpl in *.
      exists (vNeu _ _ _ n0 s i)...
    +
      destruct s; try discriminate...
      inversion H1; subst...
      exists (vELam _ _ v t1 s)...
    +
      dependent destruction l; try discriminate; inversion H1; subst.
      assert (Subset zs xs)...
      unfold Subset in *; intros; eauto.
      eapply s; eauto.
      apply set_union_intro1...
      exists (vStruct _ _ H0 s0)...
    +
      destruct s0; try discriminate; inversion H1; subst.
      assert (Subset zs xs)...
      unfold Subset in *; intros; eauto.
      eapply s; eauto.
      apply set_union_intro1...
      exists (vStruct _ _ H0 s0_1)...
    +
      dependent destruction i; try discriminate; inversion H1; subst...
      simpl in *.
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; eauto.
      eapply s; eauto.
      apply set_union_intro1...
      exists (vStruct _ _ H0 s0)...
      exists (vNeu _ _ _ n s i)...
    +
      destruct s; try discriminate.
    +
      destruct l; try discriminate; inversion H1; subst...
      simpl in *. 
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      assert (Subset xs0 (x1 :: ys)).
      unfold Subset in *; intros; eauto.
      case_eq (eq_var x x1); intros; subst; eauto.
      left; auto.
      right; eauto.
      assert (In x ys0).
      clear H1 H3 H l s2.
      induction i; simpl; eauto.
      elim H2; subst; intros; subst...
      elim n1...
      elim H2; intros; subst...
      right...
      eapply IHi; intros...
      eapply s1...
      destruct (set_union_elim _ _ _ _ H1); intros...
      apply set_union_intro1...
      apply set_union_intro2...
      right...
      inversion n...
      intro.
      elim n0...
      right...
      apply s1...
      apply set_union_intro2...
      exists (vCLam _ _ H2 l)...
    +
      destruct s2; try discriminate; inversion H1; subst.
      elim struct_to_term_injective with s0 _ s2_1; intros; subst...
      assert (Subset xs0 (x1 :: ys)).
      unfold Subset in *; intros; eauto.
      case_eq (eq_var x x1); intros; subst; eauto.
      left; auto.
      right; eauto.
      rewrite (proof_irrelevance _ Hnd Hnd0) in *.
      assert (In x ys0).
      clear H3 H H1 s2_1 s2_2.
      induction i; simpl; eauto.
      elim H2; subst; intros; subst...
      elim n1...
      elim H2; intros; subst...
      right...
      eapply IHi; intros...
      eapply s1...
      destruct (set_union_elim _ _ _ _ H1); intros...
      apply set_union_intro1...
      apply set_union_intro2...
      right...
      inversion n...
      intro.
      elim n0...
      right...
      apply s1...
      apply set_union_intro2...
      exists (vStruct _ _ H2 s2_2)...
    +
      dependent destruction i; try discriminate; inversion H1; subst...
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      assert (Subset zs (x :: ys))...
      unfold Subset; intros...
      case_eq (eq_var x x0); intros; subst...
      left...
      right...
      apply s1.
      apply set_union_intro2...
      apply set_remove_3...
      assert (~ In y (x :: ys))...
      intro.
      destruct H4; subst...
      exists (vNeu _ _ _ H4 H2 i)...
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ H3)...
      unfold Subset in *; intros; subst; eauto.
      elim n.
      auto.
    +
      destruct s1; try discriminate.
  Qed.
  
  
  (* A value is not a redex. *)
  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
      value_to_term v <> redex_to_term r.
  Proof with eauto.
    intros k v r.
    dependent destruction r.
    dependent destruction v; intro H; inversion H; dependent destruction s0; try discriminate; (rewrite (proof_irrelevance _ Hnd0 Hnd) in *  || idtac).
    +
      rewrite <- x in H1.       
      destruct l; try discriminate; inversion H1; subst.
    +
      destruct l; try discriminate; inversion H1; subst...
    +
      rewrite <- x0 in H1.
      inversion H1; subst.
    +
      simpl in *.
      inversion H1; subst.
      destruct s0; destruct s1; try discriminate; inversion H2; subst.
      eelim struct_not_sub_lambda...
    +    
      destruct s0; try discriminate; inversion H1; subst...
    +
      rewrite <- x0 in H1.
      inversion H1; subst.
    +
      rewrite <- x in H1.
      destruct i; try discriminate; inversion H1; subst.
      inversion H2; subst.
      eelim inctx_E_not_sub_lambda with (s0:=subMt) (v:=v1) (r:=t)...
      eelim struct_not_sub_lambda  with (s0:=subMt) (v:=v1) (r:=t)...
    +
      rewrite <- x in H1.
      destruct i; try discriminate; inversion H1; subst.
      dependent destruction i; try discriminate.
      inversion H2; subst.
      eelim inctx_E_not_sub_lambda...
      destruct s1; try discriminate; inversion H2; subst.
      eelim struct_not_sub_lambda...
    +
      inversion H1; subst.
      destruct s; discriminate.
    +
      rewrite <- x in H1.
      destruct s; discriminate.
    +
      dependent destruction v; intro H; inversion H.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      inversion H1; subst.
      dependent destruction l; try discriminate;
        inversion H1; subst...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      inversion H1; subst.
      destruct s0; try discriminate; inversion H1; subst;
        inversion H1; subst.
      eelim struct_not_sub_lambda...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      inversion H1; subst.
      dependent destruction i; try discriminate; inversion H1; subst...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      simpl in *.
      rewrite <- x in H.
      inversion H1; subst.
      destruct s; discriminate.
    +
      dependent destruction v; intro H; inversion H...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      simpl in *.
      rewrite <- x in H.
      dependent destruction l; try discriminate.
      simpl in *.
      inversion H1; subst.
      assert (hh:=lambda_normal_vars_neutral _ l _ _ _ i H4).
      elim n...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      destruct s0; try discriminate; inversion H1; subst.
      assert (hh:=struct_vars_neutral _ _ _ _ _ _ H4)...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      dependent destruction i; try discriminate; inversion H1; subst.
      elim (neutral_to_term_vars i _ _ i0); intros...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H1.
      destruct s; try discriminate; inversion H1; subst.
      eelim inctx_E_not_sub_lambda...
    +
      intro H.
      dependent destruction v.
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct l; simpl in *; try discriminate.
      inversion H; subst...
      inversion H; subst...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      simpl in H.
      destruct s0; simpl in *; try discriminate.
      inversion H; subst...
      elim struct_to_term_injective with s0_1 _ s3; intros; subst...
      elim struct_to_term_injective with s0_2 _ s4; intros; subst...
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct i; simpl in *; try discriminate.
      inversion H; subst...
      inversion H; subst...
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct s; simpl in *; try discriminate.
    +
      intro H.
      dependent destruction v.
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct l; simpl in *; try discriminate.
      inversion H; subst...
      elim struct_to_term_injective with s3 _ s2; intros; subst...
      elim lambda_normal_to_term_injective with l _ l0; intros; subst...
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct s0; simpl in *; try discriminate.
      inversion H; subst...
      simpl in *.
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct i; simpl in *; try discriminate.
      inversion H; subst...
      inversion H; subst...
    +
      intro H.
      simpl in *.
      dependent destruction v; try discriminate...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct s0; try discriminate.
      simpl in *.
      inversion H; subst...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      dependent destruction i; try discriminate.
      simpl in *.
      inversion H; subst...
      simpl in *.
      inversion H; subst...
      rewrite (proof_irrelevance _ Hnd0 Hnd) in *.
      rewrite <- x in H.
      destruct s; discriminate.
  Qed.
  
  (* There are no other potential redices inside a potential redex; 
           there can be only values. *)
  Lemma redex_trivial1 :
    forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
      ec:[t] = r -> exists (v : value k'), t = v.
  Proof with eauto.
    intros ? ? r ec t H.
    dependent destruction ec; dependent destruction r;
      subst; rewrite (proof_irrelevance _ Hnd0 Hnd) in *; rewrite <- x in *;
        simpl in *; inversion H; subst...
    +
      exists (vELam _ _ v  t s)...
    +
      eelim struct_not_sub_lambda...
    +
      exists (vNeu _ _ _ n s i)...
    +
      simpl in *.
      exists (vELam _ _ v t s)...
    +
      exists (vStruct _ _ s s1)...
    +
      exists (vStruct _ _ s s1)...
    +
      simpl in *.
      exists (vStruct _ _ s s0)...
    +
      eelim struct_not_sub_lambda...
    +
      elim struct_to_term_injective with s4 _ s1; intros; subst...
      assert (Subset zs (x0 :: ys)).
      unfold Subset in *; intros; eauto.
      right...
      exists (vStruct _ _ H1 s2)...
    +
      assert (Subset zs (x0::ys)).
      unfold Subset in *; intros; eauto.
      right; auto.
      exists (vCLam _ _ H0 l)...
    +
      elim struct_to_term_injective with s3 _ s0; intros; subst...
      exists (vELam _ _ v t s1)...
  Qed.
  

  
  
End Lam_cbnd_PreRefSem.


(* The module type REF_STRATEGY is defined in the file *)
(*     refocusing/refocusing_semantics.v. *)
Module Lam_cbn_Strategy <: REF_STRATEGY Lam_cbnd_PreRefSem.
  
  Import Lam_cbnd_PreRefSem.

  (* Here we define the two functions: up arrow and down arrow. *)
  Inductive elem_dec k : Type :=
  | ed_red  : redex k -> elem_dec k
  | ed_dec : forall k', term -> elem_context_kinded k k' -> elem_dec k
  | ed_val  : value k -> elem_dec k.
  Arguments ed_red {k} _.       Arguments ed_val {k} _.
  Arguments ed_dec {k} k' _ _.


  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)  
  

  Definition dec_term (t : term) k : elem_dec k.
    refine(
        match k with 
        | ckv E xs Hnd => (* decomposition under weak strategy *)
          match t with
          | App t1 t2 => ed_dec _ t1 (k_ap_r _ t2) 
          | Var x     => 
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => ed_val (vStruct _ _ _ (sVar x)) (* x is struct *)
            | right p => ed_val (vNeu _ _ _ _ _ (inctxVar x)) (* x is active var in ctx *)
            end
          | Lam x t1  => ed_val (vELam _ _ x t1 subMt) (* lambda - weak value *)
          | Let x t1 t2 => 
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in let *)
              let f := fresh_for xs in
              ed_dec (ckv E xs Hnd) ([x:=Var f] t2)
                     (in_let _ f _ (fresh_for_is_fresh f xs _) t1)
            | right p => ed_dec (ckv E xs Hnd) t2 (in_let _ x _ p t1)
            end 
          | LetNd x t n => ed_dec _ t (let_var _ _ _ n) (* x is needed - decompose t *)
          end
        | ckv C xs Hnd => (* decomposition under strong strategy *)
          match t with
          | App t1 t2 => ed_dec _ t1 (k_ap_r _ t2)
          | Var x     => 
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => ed_val (vStruct _ _ _ (sVar x)) (* x is struct *)
            | right p => ed_val (vNeu _ _ _ _ _ (inctxVar x)) (* x is active var in ctx *)
            end
          | Lam x t1  => 
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in lam *)
              let f:= fresh_for xs in
              ed_dec _  ([x := Var f] t1) (k_lam_c f _ (fresh_for_is_fresh f xs _))
            | right p => ed_dec _  t1 (k_lam_c x _ p)
            end 
          | Let x t1 t2 => 
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in let *)
              let f:=fresh_for xs in
              ed_dec (ckv C xs Hnd) ([x:=Var f] t2)
                     (in_let _ f _ (fresh_for_is_fresh f xs _) t1)
            | right p => ed_dec (ckv C xs Hnd) t2 (in_let _ x _ p t1)
            end 
          | LetNd x t n => ed_dec _ t (let_var _ _ _ n) (* x is needed - decompose t *)
          end
        end); eauto.
  Defined.


  
  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)

  Lemma dec_term_correct : 
    forall (t : term) k, match dec_term t k with
                    | ed_red r      => t = r
                    | ed_val v      => t = v
                    | ed_dec _ t' ec => t = ec:[t']
                    end.
  Proof.
    destruct k,t,c ; simpl; auto;
      case_eq (in_dec eq_var v xs); intros; auto.
    simpl.
    admit. (* alpha-renaming *)
    simpl.
    admit. (* alpha-renaming *)
    simpl.
    admit.
  Admitted.


  

  Definition dec_context
     {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k.
    refine(
        match ec in eck k k' return val k' -> elem_dec k with
        | @k_lam_c xs x Hnd _   =>
          fun v => 
            match v in val k' return k' = ckv C _ _ -> elem_dec _ with
            | vELam ys x _ t0 s => fun h1 => _ (* absurd case *)
            | @vNeu C l y ys _ _ _ s  =>
              fun h2 => 
                match eq_var x y with
                | left p => ed_dec  _ s (k_lam_c _ _ _)
                | right p => ed_val (vNeu _ _  _ _ _ (inctxLam _ y _ _  s))
                end 
            | @vNeu E _ _ _ _ _ _ s  => fun h2 => _ (* absurd case *)
            | @vCLam ys _ _ _ l1  =>
              fun h3 => ed_val (vCLam _ _ _ (lnfLam _ _  (nf_lam_in_ctx _ _)))
            | @vStruct E _ _ _ _ s => fun h4 => _ (* absurd case *)
            | @vStruct C l _ _ _ s =>
              fun h5 => ed_val (vCLam _ _ _ (lnfLam x  _ (nf_struct _ _)))
            end refl_equal
        | @k_ap_r xs _ _ t =>
          fun v =>
            match v in val k' return k' = ckv E _ _ -> elem_dec _ with
            | vELam ys _ x t0 s =>
              fun h1 => ed_red (@rApp _ _ _ x t0 s t) 
            | @vNeu E _ _ _ _ _ _ s    =>
              fun h2 => ed_val (vNeu _ _ _ _ _ (inctxApp_l _ _ _ s t))
            | @vNeu C _ _ _ _ _ _ s    => _ (* absurd case *)
            | vCLam _ _ _ _  => fun _ =>  _ (* absurd case *)
            | @vStruct E ys zs _ _ s =>
              fun h4 => ed_dec _ t (k_ap_l_E _ _ _ _ s)
            | vStruct _ _ _ _ => fun h5 => _ (* absurd case *)
            end refl_equal
        | k_ap_l_E _ _ _ _ v0  =>
          fun v => match v in val k' return k' = ckv C _ _ -> elem_dec _ with
                  | vELam _ y v0 _ s => fun h6 => _  (* absurd case *)
                  | @vNeu E _ _ _ _ _ _ _  => _ (* absurd case *)
                  | @vNeu C _ _ _ _ _  _ s    =>
                    fun h7 => ed_val (vNeu _ _ _ _ _ (inctxApp_r _ _ _ _ v0 s))
                  | vCLam _ _ _ l =>
                    fun h8 => ed_val (vStruct _ _ _ (sApp _ _ v0 (nf_lam_in_ctx _ l)))
                  | @vStruct C _ _ _ _ s =>
                    fun h9 => ed_val (vStruct _ _ _ (sApp _ _ v0 s)) 
                  | vStruct _ _ _ _ => fun h10 => _ (* absurd case *)
                  end refl_equal 
        | @in_let E ys x _ _ t =>
          fun v => 
            match v in val k return k= ckv E _ _ -> elem_dec _ with
            | vELam _ y v0 _ s => fun h11 => _
            (* ed_val (vELam _ y v0 _ (subCons x t s)) *)
            | vNeu v2 _ _ _ _ s    => fun h12 => 
                                       match eq_var x v2 with
                                       | left _ => _
                                       | right _ => _
                                       end
            (*ed_dec _ t (let_var _ x _ (s:term)) *)
            | vCLam _ _ _ _  => fun h13 => _ (* absurd case *)
            | @vStruct E _ _ _ _ s =>
              fun h14 => ed_val (vStruct _ _ _ (sSub x _ _ t s)) 
            | vStruct _ _ _ _ => fun h15 => _ (* absurd case *)
            end refl_equal 
        | @in_let C ys x _ _  t =>
          fun v => 
            match v in val k return k= ckv C _ _ -> elem_dec _ with
            | vELam _ y v0 _ s => fun h16 => _ (* absurd case *)
            | vNeu v2 _ _ _ _ s    =>
              fun h17 => 
                match eq_var x v2 with
                | left _ => _
                | right _ => _
                end
            (*ed_dec _ t (let_var _ x _ (s:term))*)
            | vCLam _ _ _ ln  =>
              fun h18 => ed_val (vCLam _ _ _ (lnfSub _ _ _  t ln))
            | @vStruct E _ _ _ _ s => fun h19 => _ (* absurd case *)
            | vStruct _ _ _ s =>
              fun h20 => ed_val (vStruct _ _ _ (sSub x _ _ t s))
            end refl_equal 
        | @let_var k xs x _ t =>
          fun v => 
            match v in val k' return k' = ckv E _ _ -> elem_dec (ckv k _ _) with
            | vELam _ _ y v0 s =>
              fun h21 => ed_red (rSub x _ t y  v0 s)
            | @vNeu E _ y _ _ _ _ s    =>
              fun h22 => ed_val (vNeu y _  _  _ _ (@inctxNdSub2 _ y _ x s  t ))
            | @vNeu C _ _ _ _ _ _ _    => _ (* absurd case *)
            | vCLam _ _ _ _ => fun h23 => _ (* absurd case *)
            | @vStruct E ys zs _ _ s => fun h24 => _
            (*ed_dec _ t _ (let_var2 _ _ _ _ _ s) 
                          match In_dec eq_var x xs with
                          | left p => ed_val _
                          | right p => ed_dec _ t (let_var2 _ _ _ _  _ s)
                          end*)
            | vStruct _ _ _ _ => fun h25 => _ (* absurd case *)
            end refl_equal 
        | @let_var2 C x _ _ _ _ _ s1  =>
          fun v => 
            match v in val k' return k' = ckv C (x::_) _ -> elem_dec _ with
            | vELam _ y v0 _ s =>  fun h26 => _ (* absurd case *)
            | vNeu l y ys _ _ s    => fun h27 => _ 
            | vCLam l _ _ nl => fun h28 => _
            (*                          match In_split x l with
                                              | inleft (exist _ ll _) => ed_val (vCLam _ _ _)    
                                              | inright p => ed_val _
                          end   *)            
            | @vStruct E l _ _ _ s => fun h29 => _ (* absurd case *)
            | @vStruct C l _ _ _ s => fun h30 => _
            (*match In_split x l with
              | inleft (exist _ ll _) => ed_val _
              | inright p => ed_val (vStruct _ _ (nSub x _ _ (s1:term) s))
              end  *)
            end refl_equal
        | @let_var2 E x _ _ _ _ _ s1  =>
          fun v => 
            match v in val k' return k' = ckv E (x::_) _ -> elem_dec _ with
            | vELam _ y v0 _ s =>  fun h261 => ed_red _
            (* ed_val (vELam _ y v0 _ (subCons x (s1:term) s))*)
            | @vNeu _ l y ys _ _ _ s    => fun h271 => _
            (*match In_split x l with
              | inleft (exist _ ll _) => ed_val (vNeu _ _ _ _ (inctxNdSub _ _ _ _ _ _ s1 _))       
              | inright p => _
              end*)  
            | vCLam l _ _ nl => _ (* absurd case *)
            | @vStruct E _ l _ _ s => fun h291 => _
            (*                         match In_split x l with
                                       | inleft (exist _ ll _) => ed_val _
                          | inright p  => ed_val (vStruct _ _ (nSub x _ _ (s1:term) s))  
                          end  *) 
            | @vStruct C _ _ _ _ s => fun h301 => _ (* absurd case *)
            end refl_equal
        end v); try solve [discriminate];
      match goal with
      | [ H : ckv _ _ _ = ckv _ _ _ |- _ ] => inversion H; subst; eauto
      | _ => idtac
      end;
      unfold Subset in *; intros; eauto.
    + (* h3 *)
      (*    instantiate (1:=x) in H.*)
      case_eq (eq_var x x0); intros; subst; eauto.
      elim set_remove_2 with _ eq_var x0 x0 ys; eauto.
      assert (hh:=set_remove_1 _ _ _ _ H).
      destruct (s _ hh); subst; eauto.
      elim n1; auto.
    +
      assert (hh:=set_remove_1 _ _ _ _ H).
      assert (gh:=s0 _ hh).
      destruct gh; subst...
      assert (NoDup l) by eauto.
      elim (set_remove_2 _ H0 H); eauto.
      auto.
    +
      intro.
      elim n1...
      right; auto.
    +
      assert (hh:=set_remove_1 _ _ _ _ H).
      assert (gh:=s0 _ hh).
      destruct gh; subst...
      eelim (set_remove_2 _ _ H); eauto.
      auto.
    +
      assert (hh:=set_union_elim _ _ _ _ H).
      destruct hh; subst; eauto.
    +
      assert (hh:=set_union_elim _ _ _ _ H).
      destruct hh; subst; eauto.
    +
      assert (hh:=set_union_elim _ _ _ _ H).
      destruct hh; subst; eauto.
    + 
      exact (ed_red (rSubNd v2 _ _ s0 s t)).
    +
      assert (~ @In var x s1) by eauto.
      exact (ed_val (vNeu _ _ _ n2 s0 (inctxSub x _ _ n3 H s t))).
    +
      exact (ed_val (vELam _ n v0 t0 (subCons x t s))).
    +
      exact (ed_red (rSubNd v2 _ _ s0 s t)).
    +
      assert (~@In var x s1) by eauto.
      exact (ed_val (vNeu _ _ _ n2 s0 (inctxSub x _ _ n3 H s t))).
    +
      case_eq (@In_split var eq_var x xs); intros.
      auto.
      destruct s1.
      destruct s1.
      destruct a.
      subst.
      remember (fresh_for (x0++x::x1)) as f.
      exact (ed_dec _ ([x:=#f]t) (let_var2 f _ _ _ (fresh_for_is_fresh f (x0++x::x1) (eq_sym Heqf)) s0 s)). 
      exact (ed_dec _ t (let_var2 x _ _ _  n1 s0 s)).
    +
      assert (NoDup s2) by eauto.
      assert (hh:=@In_split var eq_var x s2 H).
      destruct hh; subst.
      repeat destruct s5.
      destruct a; subst.
      assert (Subset (set_union eq_var s4 (x0++x1)) l0).
      unfold Subset in *; intros; eauto.
      assert (hh:=set_union_elim _ _ _ _ H0).
      destruct hh; subst; eauto.
      assert (gg:=in_app_or _ _ _ H2).
      destruct gg; subst.
      assert (In x2 (x0++x::x1)).
      apply in_or_app; auto.
      assert (hh:=s3 _ H4).
      destruct hh; subst; eauto.
      elim H1.
      apply in_or_app.
      left; auto.
      assert (In x2 (x0++x::x1)).
      apply in_or_app; auto.
      right; auto.
      right; auto.
      assert (hh:=s3 _ H4).
      destruct hh; subst; eauto.
      elim H1; eauto.
      assert (in_split x (x0++x1) (x0 ++ x :: x1)).
      apply in_split_split; eauto.
      eapply NoDup_remove_1; eauto.
      assert (NoDup (x0++x1)).
      eapply NoDup_remove_1; eauto.
      assert (~In x x1) by eauto.
      exact (ed_val (vStruct _ _ H0 (sNdSub x _ _ _ H2 H3 H1 s1 s))).
      assert (Subset s2 l0); eauto.
      unfold Subset in *; intros; eauto.
      assert (hh:=s3 _ H0).
      destruct hh; subst; eauto.
      elim n2; eauto.
      exact (ed_red (rSubWrong x _ _ _  s0 H0 n2 s1 s)).
    +
      assert (~In y l0).
      intro; elim n2.
      right; auto.
      assert (Subset (set_union eq_var s3 (set_remove eq_var x l)) l0).
      unfold Subset in *; intros.
      assert (hh:=set_union_elim _ _ _ _ H0).
      destruct hh; subst; eauto.
      assert (In x0 l).
      assert (NoDup l) by eauto.
      assert (gg:=set_remove_2 _ H2  H1).
      apply set_remove_1 with eq_var x; eauto.
      assert (hh:=s2 _ H2).
      destruct hh; subst; eauto.
      eelim (set_remove_2 _ _ H1); eauto.
      assert (x<>y). 
      intro; elim n2; eauto.
      subst; eauto.
      left; auto.
      assert (~In y s3) by eauto.
      exact (ed_val (vNeu _ _ _ H H0 (inctxNdSub x y _ _ H1 H2 s1 s))).  
    +
      exact (rSubNdE x _ _ s0 s1 v0 t s).
    +
      destruct (@In_split var eq_var x s2).
      eauto.
      assert (NoDup s2) by eauto; auto.
      destruct s4.
      destruct s4.
      destruct a.
      subst.
      assert (~In x x0) by eauto.
      assert (in_split x (x0 ++ x1) (x0 ++ x :: x1)).
      apply in_split_split; eauto.
      assert (NoDup (x0++x::x1)) by eauto.
      eapply NoDup_remove_1; eauto.
      assert (NoDup (x0 ++ x1))...
      assert (NoDup (x0++x::x1)) by eauto.
      apply NoDup_remove_1 with x; eauto.
      remember (lnfNdSub x (x0++x1) _ _  H2 H3 H1 s1 nl) as vv.
      assert (Subset (set_union eq_var s (x0 ++ x1)) l0).
      unfold Subset in *; intros; subst; eauto.
      assert (hh:=set_union_elim _ _ _ _ H4).
      destruct hh; subst; eauto.
      assert (gh:=in_app_or _ _ _ H5).
      destruct gh; subst; eauto.
      assert (In x2 (x0 ++ x :: x1)) by eauto.
      assert (gg:=s3 _ H7).
      destruct gg; subst; eauto.
      elim H1; eauto.
      assert (In x2 (x0 ++ x :: x1)).
      apply in_or_app.
      right; right; auto.
      assert (gg:=s3 _ H7).
      destruct gg; subst; eauto.
      elim H1; eauto.
      exact (ed_val (vCLam _ _ H4 vv)).
      (* !!!!!!!!!!!!!! *)
      assert (Subset (set_union eq_var  s s2) l0).
      unfold Subset in *; intros; subst; eauto.
      assert (hh:=set_union_elim _ _ _ _ H).
      destruct hh; subst; eauto.
      assert (gg:=s3 _ H0).
      destruct gg; subst; eauto.
      elim n2; eauto.
      assert (Subset s2 l0).
      unfold Subset in *; intros; subst.
      assert (hh:=s3 x0 H0).
      destruct hh; eauto.
      subst.
      elim n2; eauto.
      exact (ed_red (rSubWrong2 x _ _  _ s0 H0 n2 s1 nl)). 
    +
      assert (NoDup l) by eauto.
      assert (hh:=@In_split var eq_var x l H).
      repeat destruct hh.
      destruct s4.
      destruct s4.
      destruct a.
      subst.
      assert (in_split x (x0 ++ x1) (x0 ++ x :: x1)) .
      apply in_split_split; eauto.
      eapply NoDup_remove_1; eauto.
      assert (NoDup (x0 ++ x1)) .
      apply NoDup_remove_1 with x; auto.
      remember (sNdSub x (x0++x1) _ _ H0 H2 H1 s1 s) as vv.
      assert (Subset (set_union eq_var s3 (x0 ++ x1)) l0).
      unfold Subset in *; intros; subst; eauto.
      assert (hh:=set_union_elim _ _ _ _ H3).
      destruct hh; subst; eauto.
      assert (gh:=in_app_or _ _ _ H4).
      destruct gh; subst; eauto.
      assert (In x2 (x0 ++ x :: x1)) by eauto.
      assert (gg:=s2 _ H6).
      destruct gg; subst; eauto.
      elim H1; eauto.
      assert (In x2 (x0 ++ x :: x1)).
      apply in_or_app.
      right; right; auto.
      assert (gg:=s2 _ H6).
      destruct gg; subst; eauto.
      elim H1; eauto.
      exact (ed_val (vStruct _ _ H3 (sNdSub x _ _ _ H0 H2 H1 s1 s))).
      assert (Subset l l0).
      unfold Subset in *; intros; subst; eauto.
      elim (s2 _ H0); intros; subst; eauto.
      elim n2; eauto.
      exact (ed_red (rSubWrong x _ _ _ s0 H0 n2 s1 s)).
    +
      assert (x<>l).  
      intro; subst.
      apply n1...
      left; auto.
      assert (~ In l l0).
      intro.
      elim n1; eauto.
      right; auto.  
      assert (~ In l s4) by eauto. 
      assert (Subset (set_union eq_var s4 (set_remove eq_var x s2)) l0).
      unfold Subset in *; intros; eauto.
      assert (hh:=set_union_elim _ _ _ _ H2).
      destruct hh; subst; eauto.
      assert (In x0 s2).
      assert (hh:=set_remove_1 eq_var _ _ _ H3).
      auto.
      assert (hg:=s3 _ H4).
      destruct hg; subst; eauto.
      eelim (set_remove_2 _ _ H3); eauto.
      exact (ed_val (vNeu _ _ _ H0 H2 (inctxNdSub _ _ _ _ H H1 s1 s))).
      Unshelve.
      eauto.
      eauto.
      eauto.
  Defined.


  (* The two pairs (term, context) before and after decomposition represent *)
  (* the same term. *)
  Lemma dec_context_correct :         forall {k k'} (ec : elem_context_kinded k k') v,
      match dec_context ec v with
      | ed_red r        => ec:[v] = r
      | ed_val v'       => ec:[v] = v'
      | ed_dec _ t ec' => ec:[v] = ec':[t]
      end.
  Proof with eauto.
    intros ? ? ec v.
    dependent destruction ec; dependent destruction v;
      try rewrite (proof_irrelevance _ Hnd0 Hnd) in *;
      try rewrite (proof_irrelevance _ Hnd0 (NoDup_cons Hnd HIn)) in *;
      try rewrite <- x in *;
      try ( simpl; solve [ eauto ]);
      try dependent destruction k;
      cbn; try (case_eq (eq_var x1 x0)); intros; subst; simpl; eauto.
    +
      case_eq (@In_split var eq_var x0 xs Hnd); intros; subst; eauto.
      repeat destruct s1.
      destruct a; subst.
      cbn.
      admit. (* alpha *)
    
    +
      case_eq (@In_split var eq_var x0 xs Hnd); intros; subst; eauto.
      repeat destruct s1.
      destruct a; subst.
      cbn.
      admit. (* alpha *)
    +
      case_eq (@In_split var eq_var x0 xs0 (lambda_normal_NoDup l)); intros; subst; eauto.
      repeat destruct s2.
      destruct a; subst.
      cbn; 
      simpl.
      auto.
     +
       case_eq (@In_split var eq_var x0 xs0 (struct_NoDup s2)); intros; subst...
      repeat destruct s3.
      destruct a...
      subst.
      cbn; 
      simpl.
      auto.
     +
       case_eq (@In_split var eq_var x0 xs0 (struct_NoDup s2)); intros; subst...
      repeat destruct s3.
      destruct a...
      subst.
      cbn; 
      simpl.
      auto.
  Admitted.

  (* Here we define an order on elementary contexts. *)
  (* This is necessary to make the generated machine deterministic. *)
  
  Inductive elem_context_in k : Type :=
  | ec_in : forall k' : ckind, elem_context_kinded k k' -> elem_context_in k.
  Arguments ec_in {k} _ _.
  Coercion ec_kinded_to_in {k1 k2} (ec : elem_context_kinded k1 k2) := ec_in k2 ec.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context_in k) : Prop := 
    let (_, ec)  := ec  in
    let (_, ec0) := ec0 in
    match ec, ec0 with 
    | k_ap_l_E _ _ _ _ _, k_ap_r _ _ => immediate_ec ec t /\ immediate_ec ec0 t 
    | let_var2 _ _ _ _ _ _ _ , let_var _ _ _ _=> immediate_ec ec t /\ immediate_ec ec0 t 
    | let_var2 _ _ _ _ _ _ _ , in_let _ _ _ _ _=> immediate_ec ec t /\ immediate_ec ec0 t 
    | let_var _ _ _ _ , in_let _ _ _ _ _ => immediate_ec ec t /\ immediate_ec ec0 t 
    | _, _           => False
    end.

  
  Ltac prf :=
    match goal with
    | [ H : NoDup _, H1 : NoDup _ |- _  ] => (assert (H=H1) by apply proof_irrelevance; dep_subst; try contradiction; try auto)
    end.

  (* But we still have to go through all of the following. *)
  Notation "t |~  ec1 << ec2 "     := (search_order _ t ec1 ec2)
                                       (at level 70, ec1, ec2 at level 50, no associativity).

  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
                                       (no associativity, at level 70, ec1, t at level 69).

  (* The search order is well-founded. *)
  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof.
    intros k t [? ec];
      destruct t, ec;
      constructor;
      intros [k0 ec] H;
      dependent destruction ec;
      assert (Hnd0 = Hnd) by apply proof_irrelevance;
      dep_subst;
      try rewrite <- x in *;
      try discriminate; dep_subst;
        try (inversion H; dep_subst; clear H);
        inversion H0; dep_subst; try discriminate;
          inversion H1; simpl in *; try inversion H2; dep_subst;
            (let k0 := fresh k  in
             let ec := fresh ec in
             let H  := fresh H  in
             constructor;
             intros [k0 ec] H;
             dependent destruction ec; prf;
             try rewrite <- x in *;
             try discriminate;
             try (inversion H; dep_subst; clear H)).
  Qed.
 

  (* The search order is transitive. *)
  Lemma search_order_trans :
    forall k t ec0 ec1 ec2,
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 ->
                            k,t |~ ec0 << ec2.
  Proof.
    intros k t [? ec0] [? ec1] [? ec2] H H0.
    destruct ec0; dependent destruction ec1; prf;
      try solve [ autof ].
    dependent destruction ec2; prf;
      try solve [ autof ];
    simpl;
    split;
    destruct H; auto.
    destruct H0; auto.
  Qed.

  
  (* All immediate prefixes are comparable in this order, that is: *)
  (* If we have two productions in the grammar of the form  k-> ec0[k'] and *)
  (* k-> ec1[k''] and the two elementary contexts are prefixes of the same term, *)
  (* then they are comparable. *)
  Lemma search_order_comp_if :
    forall t k k' k'' (ec0 : elem_context_kinded k k')
      (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  (k' = k'' /\ ec0 ~= ec1).
  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.
    destruct H0 as (t0, H4); destruct H1 as (t1, H5);
      subst t;
      destruct ec0; dependent destruction ec1;
        assert (Hnd0 = Hnd) by apply proof_irrelevance;
        dep_subst;
        try discriminate;
        subst;
        inversion H5;
        subst;
        try (rewrite (proof_irrelevance _ HIn HIn0) in *);
             try (elim struct_to_term_injective with s2 _ s0;
                  intros; subst; auto;
                  inversion H5; dep_subst;
                  rewrite proof_irrelevance with _ s s1);
             try rewrite proof_irrelevance with _ n n0;
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
  Proof with eauto.
    intros t k k'' k''' ec0 ec1 H.
    destruct ec0; dependent destruction ec1; prf;
        subst;
        inversion H;
        solve [auto].
  Qed.

  
  (* Order-related definitions *)
  
  Definition so_maximal {k} (ec : elem_context_in k) t :=
    forall (ec' : elem_context_in k), ~ t |~ ec << ec'.
  Definition so_minimal {k} (ec : elem_context_in k) t :=
    forall (ec' : elem_context_in k), ~ t |~ ec' << ec.
  Definition so_predecessor
             {k}
             (ec0 : elem_context_in k) (ec1 : elem_context_in k) t :=
    (*1*) t |~ ec0 << ec1 /\
    (*2*)                                              forall (ec : elem_context_in k),
      t |~ ec << ec1  ->  ~ t |~ ec0 << ec.
  
  Hint Unfold so_maximal so_minimal so_predecessor.

  
  (* The down-arrow function always chooses the maximal element. *)
  Lemma dec_term_term_top : forall {k k'} t t' (ec : elem_context_kinded k k'),
      dec_term t k = ed_dec _ t' ec -> so_maximal ec t.
  Proof.
    intros k k' t t' ec H ec' H0. 
    destruct t, ec; dependent destruction ec'; destruct k';
      inversion H;
      try destruct k; try discriminate;
      match goal with
      | [ H : _  |~ _ << _  |- _ ] =>
        inversion H; dep_subst
      | _ => idtac
      end;
      match goal with
      | [ H : match in_dec eq_var ?v ?xs  with  | _ => _ end = _ |- _ ] =>
        case_eq (in_dec eq_var v xs); intros; dep_subst; eauto; rewrite H1 in *; discriminate
      | _ => idtac
      end;
    inversion H2; dep_subst;
    dependent destruction e0; try discriminate; 
       prf; try prf; auto;
    try do 2 destruct H0; try destruct H1; try discriminate;
    dependent destruction e1; 
    assert (NoDup_cons Hnd0 HIn = n) by apply proof_irrelevance; dep_subst;
      prf; contradiction.
  Qed.

 
  (* If the up-arrow function returns a redex, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from *)
  (* the minimal element. *) 
  Lemma dec_context_red_bot :  forall {k k'} (v : value k') {r : redex k}
                                      (ec : elem_context_kinded k k'),
      dec_context ec v = ed_red r -> so_minimal ec ec:[v].
  Proof.
    intros k k' ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    dependent destruction e; repeat prf;
      dependent destruction r;
      try assert (Hnd = NoDup_cons Hnd2 HIn) by apply proof_irrelevance;
      try assert (Hnd = NoDup_cons Hnd1 HIn) by apply proof_irrelevance;
      dep_subst; repeat prf;
        try dependent destruction k; try discriminate; cbn in H;
          match goal with
          | [ H : match In_split var eq_var ?x1 ?xs0 (lambda_normal_NoDup ?l) with
                | _ => _ end = _ |- _ ] => 
                                        case_eq (@In_split var eq_var x1 xs0 (lambda_normal_NoDup l)); intros s4 H0; 
                                       rewrite H0 in H; clear H0; [destruct s4 as [s10  [s20 [s30 s40] ]] | idtac]; 
                                        dep_subst; try inversion H; subst
          | [ H : match In_split var eq_var ?x1 ?xs0 (struct_NoDup ?s0) with
                | _ => _ end = _ |- _ ] => 
                                        case_eq (@In_split var eq_var x1 xs0 (struct_NoDup s0)); intros s5 H0; 
                                       rewrite H0 in H; clear H0; [destruct s5 as [s11  [s21 [s31 s41] ]] | idtac]; 
                                        dep_subst; try inversion H; subst
          | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
                | _ => _ end _ = _ |- _ ] => 
                                        case_eq (@In_split var eq_var x0 ys Hnd0); intros s6 H0; 
                                       rewrite H0 in H; clear H0; [destruct s6 as [s12  [s22 [s32 s42] ]] | idtac]; 
                                        dep_subst; try inversion H; subst
          | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
                | _ => _ end _ = _ |- _ ] => 
                                        case_eq (@In_split var eq_var x0 ys Hnd0); intros s7 H0; 
                                       rewrite H0 in H; clear H0; [destruct s7 as [s12  [s22 [s32 s42] ]] | idtac]; 
                                         dep_subst; try inversion H; subst
          | [ H : match eq_var ?x1 ?x0 with | _ => _ end = _ |- _ ] =>
             case_eq (eq_var x1 x0); intros; dep_subst;
              rewrite H0 in H; try discriminate
          | _ => idtac                                                                     
          end;
          cbn in H; inversion H; dep_subst;
            intro G;  unfold search_order in G; simpl in G;
              try    destruct G as [ G1 G2 ];
              repeat destruct G1; 
              repeat destruct G2; try discriminate;
    try (inversion H0; eelim struct_not_sub_lambda; eauto);
    try (dependent destruction e0 || dependent destruction e1);
      prf; try prf;
      dep_subst;
      try contradiction;
    try (destruct G as [G1 G2]); repeat destruct G1; repeat destruct G2;
    try inversion H0; eelim struct_not_sub_lambda; eauto.
  Qed.
        

  (* The same for the case of a value: *)
  (* If the up-arrow function returns a value, we have finished traversing the term. *)
  (* There are no further redices, i.e., we have just returned from *)
  (* the minimal element. *) 
  Lemma dec_context_val_bot :
    forall {k k'} (v : value k') {v' : value k}
           (ec : elem_context_kinded k k'),
      dec_context ec v = ed_val v' -> so_minimal ec ec:[v].
  Proof with eauto.
    intros ? ? v v' ec H [? ec'].
    destruct ec; dependent destruction ec'; dependent destruction v; prf; prf;
      try solve [ autof ];
      cbn in H;
      inversion H; dep_subst; intro H0; destruct H0; inversion H0; subst; eauto.
    inversion H2; subst; elim H4; elim n...
    case_eq (@In_split _ eq_var x1 xs Hnd1); intros; dep_subst;
      [ repeat destruct s3; repeat destruct a; dep_subst;
        cbn in H;
        rewrite H4 in H;
        inversion H |
        rewrite H4 in H;
        inversion H].
    inversion H2; subst; elim H5; elim n...
  Qed.
  
  
  (* If the up-arrow function returns that we should continue searching, *)
  (* it chooses the next (according to the order) element, that is, the predecessor. *)
  Lemma dec_context_term_next :
    forall {k0 k1 k2} (v : value k1) t
           (ec0 : elem_context_kinded k0 k1)
           (ec1 : elem_context_kinded k0 k2),
      dec_context ec0 v = ed_dec _ t ec1 -> so_predecessor ec1 ec0 ec0:[v].
  Proof with eauto.
    intros ? ? ? v t ec0 ec1 H.
    destruct ec0; dependent destruction ec1; dependent destruction v;
      repeat prf; 
      try (assert (Hnd0 = NoDup_cons Hnd1 HIn) by apply proof_irrelevance; dep_subst);
      try (rewrite <- x in *; dep_subst);
      try discriminate;
      dep_subst; 
      try (inversion H; dep_subst);
      try solve 
          [ autof ];
      try dependent destruction k; try discriminate;
        try cbn in H1;
      match goal with
      | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
              | _ => _ end _ = _ |- _ ] => let s:=fresh "s" in let h:=fresh "H" in
        case_eq (@In_split _ eq_var x0 ys Hnd0); intros s h; subst;
          [ repeat destruct s; destruct a; dep_subst;
            rewrite h in H;
            inversion H; subst;
            rewrite h in H |
            rewrite h in H;
            inversion H]
      | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
              | _ => _ end _ = _ |- _ ] =>
        let s:=fresh "s" in
        let h:=fresh "H" in
        case_eq (@In_split _ eq_var x0 ys Hnd0); intros s h; subst;
          [ repeat destruct s; destruct a; dep_subst;
            rewrite h in H;
            inversion H; subst;
            rewrite h in H |
            rewrite h in H;
            inversion H]
      | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
              | _ => _ end  = _ |- _ ] =>
        let s:=fresh "s" in
        let h:=fresh "H" in
        case_eq (@In_split _ eq_var x0 ys Hnd0); intros s h; subst;
          [ repeat destruct s; destruct a; dep_subst;
            rewrite h in H;
            cbn in H; clear h; inversion H; subst
          |
            rewrite h in H; inversion H; subst
          ];
          try destruct H6; subst

      | [ H : match eq_var ?x1 ?x0 with | _ => _ end = _ |- _ ] =>
        case_eq (eq_var x1 x0); intros; dep_subst;
          [elim n;
           left | 
           rewrite H0 in H; try discriminate]; eauto
      | [ H : match eq_var ?x1 ?x0 with | _ => _ end = _ |- _ ] =>
        case_eq (eq_var x1 x0); intros; dep_subst;
          rewrite H0 in H; try discriminate
      | _ =>  inversion H; subst; split;
                compute; eauto;
                  intros [? ec''] H0 H1; 
                  dependent_destruction2 ec'';
                  assert (Hnd=Hnd1) by apply proof_irrelevance; dep_subst;
                    try discriminate;
                    subst;
                    autof
      | _ => idtac
      end;
      simpl; repeat split; try unfold immediate_ec;
        simpl; try intros; try intro;
          match goal with
          | [ H : match ?ec with | _ => _ end |- _ ]
              => dependent_destruction2 ec; 
                   assert (s=s1) by apply proof_irrelevance; dep_subst;
                     autof;
                     dependent destruction e; try discriminate;
                       prf; dep_subst;
                         contradiction
          | _ => idtac
          end.
3 : destruct ec; 
      dependent destruction e0; try discriminate;
        prf; dep_subst;
          contradiction.
5 : destruct ec; 
      dependent destruction e0; try discriminate;
        prf; dep_subst;
          contradiction.
let s:=fresh "s" in
        let h:=fresh "H" in
        case_eq (@In_split _ eq_var x1 xs Hnd1); intros s h; subst;
          [ repeat destruct s; destruct a; dep_subst;
            rewrite h in H1;
            inversion H; subst
             |
            rewrite h in H1;
            inversion H1];
cbn in H1;
inversion H1; subst;
dependent destruction H8; subst.
split with ([x1:= (# (fresh_for (x ++ x1 :: x2)))] e);
admit.
split with t; auto.
split with s0; auto.
let s:=fresh "s" in
        let h:=fresh "H" in
        case_eq (@In_split _ eq_var x1 xs Hnd1); intros s h; subst;
          [ repeat destruct s; destruct a; dep_subst;
            rewrite h in H1;
            inversion H; subst
             |
            rewrite h in H1;
            inversion H1];
cbn in H1;
inversion H1; subst;
  dependent destruction H8; subst.
split with ([x1:=(# (fresh_for (x ++ x1 :: x2)))]e);
admit.
split with t; auto.
split with s0; auto.
  Admitted.


  (* If there are two overlapping elementary contexts in the same term, then *)
  (* the greater of them contains no redices (it contains only values). *) 
  Lemma elem_context_det :
    forall {k0 k1 k2} t (ec0 : elem_context_kinded k0 k1)
           (ec1 : elem_context_kinded k0 k2),
      t |~ ec0 << ec1 -> exists (v : value k2), t = ec1:[v].
  Proof.
    intros ? ? ? t ec0 ec1 H0.
    destruct ec0; dependent destruction ec1; prf;
      autof; 
      inversion H0; dep_subst; eauto;
        destruct H;
        destruct H1;
        simpl in *;
        rewrite <- H in H1; inversion H1; dep_subst;
    exists (vStruct _ _ s  s0); eauto.
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
Definition xx := (lambda x, (# x @ # x)).
Definition id := lambda  x, # x.
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

Extraction "strong_cbn" list_configs . 

(* and the complete machine *)
Print Lam_cbn_EAM.

(*
Add ML Path "/home/mabi/.opam/system/lib/coq/plugins/relation-extraction-master/".

Print ML Path.

Declare ML Module "extraction_plugin".
Declare ML Module "relation_extraction_plugin".

Locate dec_term.

Definition ldec_term := Lam_cbn_Strategy.dec_term.

(*Extraction Relation Relaxed Lam_cbn_EAM.trans [1 ].*)

  Inductive mytrans : configuration -> configuration -> Prop :=

  | tred : forall t {k} (c : context ick k) r,
        ldec_term t k = Lam_cbn_Strategy.ed_red r -> 
(*        contract (rApp (vLam (Id 1) (Var (Id 1))) subMt id) = Some t0 ->*)
        mytrans (<< t, c >>_e) (<< t, c >>_e).


(*Extraction Relation Relaxed mytrans [1].*)


Extraction contract.
Extraction Lam_cbn_Strategy.dec_term.

         *)

