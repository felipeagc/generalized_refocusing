(* Lambda calculus with the strong call-by-need reduction strategy *)
(* Compiles with Coq v.8.7.2 *)
(* mabi *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.


Require Import List.
Require Import Eqdep.
Require Import ListSet.
Require Import Sets.


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


  (* set of variables *)
  Definition vars := set var.


  (* E - weak cbnd, C - under lambda *)
  Inductive ck := E | C.

  (* kind is type paired with set of vars *)
  (* sets are modeled as lists with no duplication *)

  Inductive ckvars : Type :=
  | ckv : ck -> forall {xs : vars}, NoDup xs -> ckvars.

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

  Definition term := expr.
  Hint Unfold term.

  Notation " t @ s " := (App t s) (at level 40).
  Notation " # x " := (Var x) (at level 7, no associativity).
(*  Notation " '{' x '//' s '}' t " := (Let x s t) (at level 47, right associativity).
  Notation " 'let' x ':=' s 'in' t " := (LetNd x s t) (at level 47).*)
  Notation " 'λ'  x , t " := (Lam x t) (at level 50).


  Inductive (* normal forms - parameterized by minimal set of frozen variables *)
  normal : vars -> Type :=
  | nf_struct     : forall xs,        struct xs -> normal xs (*  s_{xs} ∈ n_{xs} *)
  | nf_lam_in_ctx : forall xs, lambda_normal xs -> normal xs (* ln_{xs} ∈ n_{xs} *)

  with   (* structures - parameterized by minimal set of frozen variables *)
  struct : vars -> Type :=
  | sVar : forall x, struct (x ::: ⋄) (* x ∈ s_{x} *)
  | sApp : forall xs ys,
      struct xs -> normal ys -> struct (xs +++ ys) (* s_{xs} @ n_{ys} ∈ s_{xs+ys} *)
  | sSub : forall x ys, ~ In x ys -> expr -> struct ys ->
                        struct ys (* let x = e in s_{ys} ∈ s_{ys} *)
  | sNdSub : forall x ys zs xs,
      in_split x ys xs -> NoDup ys -> ~ In x ys ->
      struct zs -> struct xs ->
      struct (zs +++ ys) (* let x:= s_{zs} in s_xs ∈ s_{zs+xs\x} *)

  with (* normal forms starting with lambda *)
  lambda_normal : vars -> Type :=
  | lnfLam : forall (x:var) xs,
      normal xs ->
      lambda_normal (set_remove eq_var x xs) (* λ x. n_{xs} ∈ ln_{xs\x} *)
  | lnfSub : forall x ys,
      ~ In x ys -> expr -> lambda_normal ys ->
      lambda_normal ys (* let x = e in ln_{ys} ∈ ln_{ys} *)
  | lnfNdSub : forall x ys zs xs,
      in_split x ys xs -> NoDup ys -> ~ In x ys ->
      struct zs -> lambda_normal xs ->
      lambda_normal (zs +++ ys) (* let x:= s_{zs} in ln_xs ∈ ln_{zs+xs\x} *).

  Scheme struct_Ind   := Induction for struct Sort Prop
    with normal_Ind := Induction for normal Sort Prop
    with lambda_normal_Ind := Induction for lambda_normal Sort Prop.

  Combined Scheme all_normal_forms_ind from struct_Ind, normal_Ind, lambda_normal_Ind.

  Fixpoint struct_to_term {xs} (s : struct xs) : term :=
    match s with
    | sVar x => # x
    | sApp xs ys s n => (struct_to_term s) @ (normal_to_term n)
    | sSub x ys _ e s => Let x e (struct_to_term s)
    | sNdSub x ys _ _ _ _ _ s sx => LetNd x (struct_to_term s) (struct_to_term sx)
    end

  with
  lambda_normal_to_term {xs} ( n : lambda_normal xs) : term :=
    match n with
    | lnfLam x xs n => λ x, (normal_to_term n)
    | lnfSub x ys _ e n => Let x e (lambda_normal_to_term n)
    | lnfNdSub x ys _ _ _ _ _ s n => LetNd x (struct_to_term s) (lambda_normal_to_term n)
    end
  with
  normal_to_term {xs} (n : normal xs) : term :=
    match n with
    | nf_struct _ s => struct_to_term s
    | nf_lam_in_ctx _ ln => lambda_normal_to_term ln
    end.

  Definition struct_to_normal {xs} (s : struct xs) : normal xs := nf_struct xs s.

  Coercion struct_to_normal : struct >-> normal.
  Coercion normal_to_term : normal >-> term.
  Coercion struct_to_term : struct >-> term.

  (* term that is decomposed as active variable in context *)
  Inductive needy : ck -> var -> vars -> Type :=
  | needyVar : forall {k} x, needy k x ⋄ (* x ∈ cˣ_{}_k *)
  | needyApp_l : forall {k} x xs,
      ~ In x xs -> needy E x xs -> expr ->
      needy k x xs (* cˣ_{xs}_E @ e ∈ cˣ_{xs}_k *)
  | needyApp_r : forall {k} x xs ys,
      ~ In x (xs ++ ys) -> struct ys ->
      needy C x xs -> needy k x (ys +++ xs) (* s_{ys} @ cˣ_{xs}_C ∈ cˣ_{ys+xs}_k *)
  | needyLam : forall x y xs,
      x <> y -> needy C y xs ->
      needy C y (set_remove eq_var x xs) (* λ x. cʸ_{xs}_C ∈ cʸ_{xs\x}_C *)
  | needySub : forall {k} x y xs,
      x <> y -> ~In x xs -> needy k y xs -> expr ->
      needy k y xs  (* let x = e in cʸ_{xs}_k ∈ cʸ_{xs}_k *)
  | needyNdSub : forall {k} x y xs zs,
      x <> y -> ~ In y xs -> struct xs -> needy k y zs ->
      needy k y (xs +++ (set_remove eq_var x zs))
  (* let x := s_{xs} in cʸ_{zs}_k ∈ cʸ_{xs+zs\x}_k *)
  | needyNdSub2 : forall {k} y xs,
      var -> needy E y xs -> expr -> needy k y xs
  (* let x := cʸ_{xs}_E in e ∈ cʸ_{xs}_k *).

  Fixpoint needy_to_term {k} {x} {xs} (nee : needy k x xs) : term :=
    match nee with
    | needyVar x => #x
    | needyApp_l x xs _ n e => (needy_to_term n) @ e
    | needyApp_r x xs ys _ s nee' => (struct_to_term s) @ (needy_to_term nee')
    | needyLam x y xs  _ nee' => λ x, (needy_to_term nee')
    | needySub x y xs _ _ n e => Let x e (needy_to_term n)
    | needyNdSub x y xs _  _ _ s n => LetNd x (struct_to_term s) (needy_to_term n)
    | needyNdSub2 y xs x ny nx => LetNd x  (needy_to_term ny) nx
    end.
  Coercion needy_to_term : needy >-> term.

  (* in terms cˣ_{xs}_k, x ∉ xs *)
  Lemma needy_var_notin_frozen :
    forall {k} x xs, @needy k x xs -> ~ In x xs.
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

  Hint Resolve needy_var_notin_frozen.

  (* notation for iteration of explicit substitutions with simple let *)
  Inductive sub : Type :=
  | subMt : sub
  | subCons : var -> expr -> sub -> sub.

  Fixpoint sub_to_term (s : sub) (t : term) :=
    match s with
    | subMt => t
    | subCons x r s' => Let x r (sub_to_term s' t)
    end.

  (* values *)
  Inductive val : ckind -> Type :=
  | vCLam : forall {xs} ys (Hnd : NoDup ys),
      Subset xs ys -> lambda_normal xs -> val (ckv C Hnd)
  (* ln_{xs} ∈ Val^{ys}_C *)
  | vStruct : forall {k} {xs} ys (Hnd : NoDup ys),
      Subset xs ys -> struct xs -> val (ckv k Hnd)
  (* s_{xs} ∈ Val^_{ys}_k *)
  | vNeedy : forall {k} {xs} x ys (Hnd : NoDup ys),
      ~In x ys -> Subset xs ys -> needy k x xs -> val (ckv k Hnd)
  (* cˣ_{xs}_k ∈ Val^{ys}_k *)
  | vELam : forall xs (Hnd : NoDup xs),
      var -> term -> sub -> val (ckv E Hnd)
  (* (Lam x. t)[sub] ∈ Val^{xs}_E *).

  Definition value := val.
  Hint Unfold value.


  Fixpoint val_to_term {k} (v : val k) : term :=
    match v with
    | vCLam _ _ _ n => lambda_normal_to_term n
    | vStruct _ _ _ s  => struct_to_term s
    | vNeedy _ _ _ _ _ n => needy_to_term n
    | vELam _ _ x t s => sub_to_term s (Lam x t)
    end.

  Coercion val_to_term : val >-> term.
  Definition value_to_term {k} := @val_to_term k.


  (* Here we define the set of potential redices. *)

  Inductive red : ckind -> Type :=
  | rApp : forall {k} {xs} {Hnd : NoDup xs},
      var -> term -> sub -> term -> red (ckv k Hnd)
  (* (Lam x. t)[sub] @ t' ∈ Red^{xs}_k *)
  | rSub : forall {k} (x: var) xs {Hnd : NoDup xs},
      term -> var -> term -> sub -> red (ckv k Hnd)
  (* Let x := (Lam y. t2)[sub] in n ∈ Red^{xs}_k *)
  | rSubNd : forall {k} x xs ys {Hnd : NoDup ys},
      Subset xs ys -> needy k x xs -> term -> red (ckv k Hnd)
  (* Let x = t in cˣ_{xs} ∈ Red^{ys}_k *)
  | rSubWrong : forall {k} x xs ys zs {Hnd : NoDup ys},
      Subset xs ys -> Subset zs ys -> ~ In x zs -> struct xs -> struct zs -> red (ckv k Hnd)
  (* Let x := s_{xs} in s_{zs} ∈ Red^{ys}_k – stuck redex *)
  | rSubWrong2 : forall x xs ys zs {Hnd : NoDup ys},
      Subset xs ys -> Subset zs ys -> ~ In x zs -> struct xs -> lambda_normal zs -> red (ckv C Hnd)
  (* Let x := s_{xs} in ln_{zs} ∈ Red^{ys}_C - stuck redex *)
  | rSubNdE : forall (x : var) xs ys {Hnd : NoDup ys},
      Subset xs ys -> struct xs -> var -> term -> sub -> red (ckv E Hnd)
  (* Let x := s_{xs} in (Lam y. t)[sub] ∈ Red^{ys}_E *).

  Definition redex := red.
  Hint Unfold redex.

  Definition redex_to_term {k} (r : redex k) : term :=
    match r with
    | rApp x t s t' => (sub_to_term s (Lam x t)) @ t'
    | rSub  x _ n y t s => LetNd x (sub_to_term s (Lam y t)) (n:term)
    | rSubNd x xs _  _ n t => Let x t (n:term)
    | rSubWrong x xs _ _ _ _ _ s s1 => LetNd x (s:term) (s1:term)
    | rSubWrong2 x xs _ _ _ _ _ s s1 =>
      LetNd x (s:term) (lambda_normal_to_term s1)
    | rSubNdE x xs _ _  s y t s0 => LetNd x (s : term) (sub_to_term s0 (Lam y t))
    end.

  Coercion redex_to_term : redex >-> term.

  Reserved Notation "'[' x ':=' s ']' t" (at level 20).

  Fixpoint subst (x:var) (s:term) (t:term) : term :=
    match t with
    | # x' =>
      if eq_var x x' then s else t
    | λ x', t1 =>
      λ x', (if eq_var x x' then t1 else ([x := s] t1))
    | t1 @ t2 =>
      ([x:=s] t1) @ ([x:=s] t2)
    | Let  x' r u => Let x' (subst x s r) (if eq_var x x' then u else [x:=s] u)
    | LetNd x1 r n =>
      LetNd x1 (subst x s r) (if eq_var x x1 then n else [ x := s ] n)
    end

  where "'[' x ':=' s ']' t" := (subst x s t).

  Fixpoint α_rename (t : expr) (x : var) (y : var) : expr :=
    match t with
    | e1 @ e2 => α_rename e1 x y @ α_rename e2 x y
    | #z => #z
    | λ z, e => if eq_var x z then λ y, [ z := #y ] e else λ z, e
    | Let z e1 e2 => if eq_var x z then Let y e1 ([ z := #y ]e2) else Let z e1 e2
    | LetNd z e1 e2 => if eq_var x z then LetNd y e1 ([ z := #y ]e2) else LetNd z e1 e2
    end.

  Axiom α_equiv :
    forall x y (e : expr), e = α_rename e x y.

  (* struct cannot begin with lambda *)
  Lemma struct_not_sub_lambda :
    forall xs (s: struct xs)  t,
      struct_to_term s = t ->
      forall v s0 r, t = sub_to_term s0 (Lam v r) ->   False.
  Proof.
    induction s; destruct t; destruct s0; try discriminate; eauto.
    intros; inversion H0; inversion H; subst; auto.
    eelim IHs; eauto.
  Qed.

  Hint Resolve struct_not_sub_lambda.

  (* struct cannot be normal form beginning with lambda *)
  Lemma struct_not_lambda :
    forall xs (s: struct xs) ys (l:lambda_normal ys),
      struct_to_term s = lambda_normal_to_term l -> False.
  Proof.
    induction s; destruct l; intros; try inversion H; subst; eauto.
  Qed.

  Hint Resolve struct_not_lambda.

  (* variable in context cannot begin with lambda *)
  Lemma needy_E_not_sub_lambda :
    forall k x xs (s: needy k x xs)  t,
      needy_to_term s = t -> forall v s0 r,
        t = sub_to_term s0 (λ v, r) -> k = E ->  False.
  Proof with eauto.
    induction s; destruct t; intros; inversion H; subst;
      try (inversion H0; dependent destruction s0; try discriminate);
      try (destruct s1; discriminate)...
    injection H0; intros...
  Qed.

  Hint Resolve needy_E_not_sub_lambda.

  Definition forall_normal_forms
   (pred :
      forall (nf_type : (vars -> Type))
             (to_term : forall {xs}, nf_type xs -> term), Prop) : Prop :=
    pred struct (@struct_to_term) /\
    pred normal (@normal_to_term) /\
    pred lambda_normal (@lambda_normal_to_term).

  Ltac assert_by_proof_irrelevance :=
    match goal with
    | [ H : ?P, H1 : ?P |- _  ] => assert (H=H1) by apply proof_irrelevance
    end.

  Ltac subst_proof_irrelevance := assert_by_proof_irrelevance; subst.
  Ltac dep_subst_proof_irrelevance := assert_by_proof_irrelevance; dep_subst.

  Lemma all_normal_forms_to_term_injective :
    forall_normal_forms (fun normal_form to_term =>
      forall {xs} (n : normal_form xs) {ys} (n' : normal_form ys),
        to_term _ n = to_term _ n' -> n ~= n' /\ xs = ys).
  Proof.
    apply all_normal_forms_ind;
    destruct n'; try discriminate;
    intros Heq; inversion Heq; subst.
    6-7: eelim struct_not_lambda; eauto.
    all: try eelim H; try eelim H0; try eelim H1; try eelim H2; intros; eauto; split; dep_subst; eauto.
    all: try (assert (hh:=in_split_inv _ _ _ _ i i0); subst; auto).
    all: repeat subst_proof_irrelevance; auto.
  Qed.

  Lemma struct_to_term_injective :
    forall {xs} (n : struct xs) {ys} (n' : struct ys),
      struct_to_term n = struct_to_term n' -> n ~= n' /\ xs = ys.
  Proof. apply all_normal_forms_to_term_injective. Qed.

  Hint Resolve struct_to_term_injective.

  Lemma lambda_normal_to_term_injective :
    forall {xs} (n : lambda_normal xs) {ys} (n' : lambda_normal ys),
      lambda_normal_to_term n = lambda_normal_to_term n' -> n ~= n' /\ xs = ys.
  Proof. apply all_normal_forms_to_term_injective. Qed.

  Lemma normal_to_term_injective :
    forall {xs} (n : normal xs) {ys} (n' : normal ys),
      normal_to_term n = normal_to_term n' -> n ~= n' /\ xs = ys.
  Proof. apply all_normal_forms_to_term_injective. Qed.

  Lemma all_normal_forms_NoDup :
    forall_normal_forms (fun normal_form _ =>
      (forall {xs} (n : normal_form xs), NoDup xs)).
  Proof with eauto.
    apply all_normal_forms_ind; intros...
    repeat constructor...
  Qed.

  Lemma struct_NoDup :
    forall {xs} (n : struct xs),
      NoDup xs.
  Proof. apply all_normal_forms_NoDup. Qed.

  Lemma lambda_normal_NoDup :
    forall {xs} (n : lambda_normal xs),
      NoDup xs.
  Proof. apply all_normal_forms_NoDup. Qed.

  Lemma normal_NoDup :
    forall {xs} (n : normal xs),
      NoDup xs.
  Proof. apply all_normal_forms_NoDup. Qed.

  Hint Resolve struct_NoDup.

  Lemma needy_NoDup :
    forall {k} {x} {xs} (n : needy k x xs),
      NoDup xs.
  Proof with auto.
    induction 1; intros...
    constructor.
  Qed.

  Hint Resolve lambda_normal_NoDup normal_NoDup needy_NoDup.

  Lemma all_normal_forms_needy_in_vars :
    forall_normal_forms (fun normal_form to_term =>
      forall xs (s: normal_form xs) k x ys (n : needy k x ys),
        to_term _ s = needy_to_term n -> In x xs).
  Proof with eauto.
    apply all_normal_forms_ind;
      simpl; intros; subst;
      match goal with
      | [ n : needy _ _ _ |- _ ] => dependent destruction n
      | _ => idtac
      end; try discriminate...
    +
      inversion H; subst...
    +
      injection H1; intros; subst...
      apply set_union_intro1; eapply H...
    +
      injection H1; intros; subst...
      apply set_union_intro2; eapply H0...
    +
      injection H0; intros; subst...
    +
      injection H1; intros; subst...
      elim struct_to_term_injective with s _ s1; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4] ] ] ; subst...
      assert (hh:=H0 _ _ _ _ H2)...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H4; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app; auto.
      auto.
    +
      injection H1; intros; subst...
      apply set_union_intro1; eapply H...
    +
      inversion H0; subst...
      apply set_remove_3...
    +
      inversion H0; subst...
    +
      inversion H1; subst...
      assert (hh:=H0 _ _ _ _ H5)...
      elim struct_to_term_injective with s _ s0; intros; subst.
      destruct (in_split_inv2 _  _ _ i) as [ h1 [ h2 [ h3 h4] ] ]; subst...
      destruct (in_app_or _ _ _ hh); eauto.
      apply set_union_intro2...
      apply in_or_app...
      destruct H2; subst; eauto.
      elim n1...
      apply set_union_intro2...
      apply in_or_app...
      auto.
    +
      inversion H1; subst...
      assert (hh:=H _ _ _ _ H4)...
      apply set_union_intro1...
  Qed.

  (* if cˣ_{ys}_k = n_{xs} then x ∈ xs *)
  Lemma normal_needy_in_vars :
    forall xs (s: normal xs) k x ys (n : needy k x ys),
      normal_to_term s = needy_to_term n -> In x xs.
  Proof. apply all_normal_forms_needy_in_vars. Qed.

  (* if cˣ_{ys}_k = ln_{xs} then x ∈ xs *)
  Lemma lambda_normal_needy_in_vars :
    forall xs (s: lambda_normal xs) k x ys (n : needy k x ys),
      lambda_normal_to_term s = needy_to_term n -> In x xs.
  Proof. apply all_normal_forms_needy_in_vars. Qed.

  (* if cˣ_{ys}_k = s_{xs} then x ∈ xs *)
  Lemma struct_needy_in_vars :
    forall xs (s: struct xs) k x ys (n : needy k x ys),
      struct_to_term s = needy_to_term n -> In x xs.
  Proof. apply all_normal_forms_needy_in_vars. Qed.

  Hint Resolve normal_needy_in_vars lambda_normal_needy_in_vars struct_needy_in_vars.

  Lemma needy_to_term_vars :
    forall {k} {x} {xs} (n : needy k x xs) y ys (n' : needy k y ys),
      needy_to_term n = needy_to_term n' -> x <> y -> In x ys \/ In y xs.
  Proof with eauto.
    induction n; intros;
      dependent destruction n'; try discriminate; inversion H; subst...
    +
      elim H0...
    +
      assert (hh:=struct_needy_in_vars  _ _ _ _ _ _ (eq_sym H2)).
      left.
      apply set_union_intro1...
    +
      assert (hh:=struct_needy_in_vars  _ _ _ _ _ _ H2).
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
      assert (hh:=struct_needy_in_vars  _ _ _ _ _ _ H3).
      right.
      apply set_union_intro; left...
    +
      assert (hh:=struct_needy_in_vars  _ _ _ _ _ _ (eq_sym H3)).
      left.
      apply set_union_intro; left...
  Qed.


  Lemma needy_to_term_injective :
    forall k x xs (n : needy k x xs) ys (n' : needy k x ys),
      needy_to_term n = needy_to_term n' ->
      @eq_dep vars (fun xs => needy k x xs) xs n ys n'.
  Proof with eauto.
    induction n; intros; dependent destruction n'; try discriminate; inversion H; subst...
    +
      assert (hh:=IHn _ _ H1).
      inversion hh; subst.
      subst_proof_irrelevance.
      dep_subst...
    +
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ (eq_sym H1)).
      elim n1...
    +
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ H1).
      elim n...
    +
      elim struct_to_term_injective with s _ s0; intros; subst.
      rewrite H0.
      destruct (IHn _ _ H2); subst...
      subst_proof_irrelevance...
      auto.
    +
      destruct (IHn _ _ H2); subst...
      subst_proof_irrelevance...
    +
      destruct (IHn _ _ H3); subst...
      repeat subst_proof_irrelevance...
    +
      elim struct_to_term_injective with s _ s0; intros; subst...
      rewrite H0.
      destruct (IHn _ _ H3); subst...
      repeat subst_proof_irrelevance...
    +
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ H2).
      elim n0...
    +
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ (eq_sym H2)).
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
      subst; repeat dep_subst_proof_irrelevance.
    +
      elim lambda_normal_to_term_injective with l _ l0; intros; subst...
      subst_proof_irrelevance...
    +
      eelim struct_not_lambda...
    +
      assert (hh:=lambda_normal_needy_in_vars _ l _ _ _ _ H1)...
      elim n...
    +
      eelim struct_not_lambda...
    +
      elim struct_to_term_injective with s0 _ s2; intros; dep_subst...
      subst_proof_irrelevance...
    +
      assert (hh:=struct_needy_in_vars _ s0 _ _ _  n0 H1).
      elim subset_not_in with xs ys x0...
    +
      eelim struct_not_sub_lambda...
    +
      assert (hh:=lambda_normal_needy_in_vars _ l _ _ _ _ (eq_sym H1))...
      elim n...
    +
      assert (hh:=struct_needy_in_vars _ s1 _ _ _  n0 (eq_sym H1)).
      elim subset_not_in with xs0 ys x0...
    +
      case_eq (eq_var x1 x0); intros; subst...
      assert (h:=needy_to_term_injective _ _ _ _ _ _ H1)...
      inversion h...
      subst...
      dependent destruction H4.
      repeat subst_proof_irrelevance...
      eelim needy_to_term_vars; intros; subst...
      elim n...
      elim n1...
    +
      eelim needy_E_not_sub_lambda...
    +
      eelim struct_not_sub_lambda...
    +
      eelim needy_E_not_sub_lambda...
    +
      eelim sub_to_term_val_injective; intros; subst...
      subst.
      inversion H0...
  Qed.


  Lemma redex_to_term_injective :
    forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.
  Proof with eauto.
    intros k r r' H.
    dependent destruction r ; dependent destruction r';
      inversion H; subst; repeat dep_subst_proof_irrelevance; inversion H1; subst...
    +
      elim sub_to_term_val_injective with s s0 v v0 t t1; intros; subst...
      inversion H2; subst...
    +
      elim sub_to_term_val_injective with s s0 v v0 t0 t2; intros; subst...
      inversion H0; subst...
    +
      simpl in *.
      inversion H1; subst.
      eelim struct_not_sub_lambda; eauto.
    +
      eelim struct_not_sub_lambda; eauto.
    +
      eelim struct_not_sub_lambda; eauto.
    +
      assert (hh:=needy_to_term_injective _ _ _ n _ n0 H3).
      inversion hh.
      dependent destruction H4.
      subst_proof_irrelevance...
    +
      eelim struct_not_sub_lambda; eauto.
    +
      elim struct_to_term_injective with s1 _ s5; intros; eauto.
      elim struct_to_term_injective with s2 _ s6; intros; eauto.
      subst...
      repeat subst_proof_irrelevance...
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
      repeat subst_proof_irrelevance...
    +
      eelim struct_not_sub_lambda with (s:=s0); eauto.
    +
      eelim struct_not_sub_lambda with (s:=s5); eauto.
    +
      elim struct_to_term_injective with s0 _ s3; intros; eauto.
      subst...
      assert (hh:=sub_to_term_val_injective _ _ _ _ _ _ H3).
      destruct hh; subst...
      inversion H4; subst...
      repeat subst_proof_irrelevance...
  Qed.


  Lemma NoDup_cons :
    forall {xs : vars}, NoDup xs -> forall {x}, ~ In x xs -> NoDup (x::xs).
  Proof.
    induction 1; simpl; intros; eauto; constructor; try intro; eauto.
    constructor.
  Qed.

  Hint Resolve NoDup_cons.

  Inductive eck : ckind -> ckind -> Type :=
  | k_lam_c : forall {xs} x (Hnd : NoDup xs) (HIn : ~In x xs),
      eck (ckv C Hnd) (@ckv C (x::xs) (NoDup_cons Hnd HIn))
  (* Lam x. []^{x,xs}_C ∈ EC^{xs}_C *)
  | k_ap_r  : forall {xs} {k} (Hnd : NoDup xs),
      term -> eck (ckv k Hnd) (ckv E Hnd) (* []^{xs}_E t ∈ EC^{xs}_k *)
  | k_ap_l_E  : forall {k} xs ys (Hnd : NoDup xs),
      Subset ys xs -> struct ys -> eck (ckv k Hnd) (ckv C Hnd)
  (* s_{ys} []^{xs}_C ∈ EC^{xs}_k *)
  | k_let : forall {k} xs (x : var) (Hnd : NoDup xs),
      ~ In x xs -> term -> eck (ckv k  Hnd) (ckv k Hnd)
  (* let x = t in []^{xs}_k ∈ EC^{xs}_k *)
  | k_definiens : forall {k} xs (x:var) (Hnd : NoDup xs),
      expr -> eck (ckv k Hnd) (ckv E Hnd) (* let x := []^{xs}_E in n ∈ EC^{xs}_k *)
  | k_letnd : forall {k} x xs ys (Hnd : NoDup ys) (HIn : ~In x ys),
      Subset xs ys -> struct xs ->
      eck (ckv k Hnd) (@ckv k (x::ys) (NoDup_cons Hnd HIn))
  (* let x := s_{xs} in []^{x,ys}_k ∈ EC^{ys}_k *).

  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.

  Notation " 'λc' x ',' '□' " := (k_lam_c x _ _) (at level 50, no associativity).
  Notation " '□' t " := (k_ap_r _ t) (at level 51).
  Notation " s '□' " := (k_ap_l_E _ _ _ _ s) (at level 51).
  Notation " 'let1' k ',' x '=' t 'in' '□' " := (@k_let k _ x _ _ t) (at level 50, x ident).
  Notation " 'let_E' x '=' t 'in' '□' " := (@k_let E _ x _ _ t) (at level 50, x ident).
  Notation " 'let_C' x '=' t 'in' '□' " := (@k_let C _ x _ _ t) (at level 50, x ident).
  Notation " 'let' k ',' x ':=' □ '^' xs 'in' t " := (@k_definiens k xs x _ t) (at level 50, x ident).
  Notation " 'let2_C' x ':=' s 'in' □ " := (@k_letnd C x _ _ _ _ _ s) (at level 50, x ident).
  Notation " 'let2_E' x ':=' s 'in' □ " := (@k_letnd E x _ _ _ _ _ s) (at level 50, x ident).
  Notation " 'let2' x ':=' s 'in' □ " := (@k_letnd _ x _ _ _ _ _ s) (at level 50, x ident).


  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  ckv C (NoDup_nil _).

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
    match ec with
    | λc x , □  => λ x , t
    | □ tr => t @ tr
    | s □  => (s : term) @ t
    | let1 _, x = s in □ => Let x s t
    | let k, x := □ ^ _ in s => LetNd x t (s:term)
    | let2 x := s in □ => LetNd x (s : term) t
    end.

  (* Here we define substitutions, which is necessary to define contraction. *)
  (* Be careful: the definition works only for closed terms s and  *)
  (* we do not check if a substitution is capture-avoiding. *)


  (* Now we are ready to define the contraction. *)


  Definition contract {k} (r : redex k) : option term :=
    match r with
    | rApp x r s t => Some (sub_to_term s (Let x t r))
    | rSub  x xs n y t s => Some (sub_to_term s (Let x (λ y, t)
                                                     (subst x (λ y, t) n)))
    | rSubNd x xs _ _ n e => Some (LetNd x e (n:term))
    | rSubNdE x xs _ _  s y t s0 => Some (Let x (s : term) (sub_to_term s0 (Lam y t)))
    | _ => None (* stuck terms *)
    end.

  (* Having this we include some basic notions *)
  Include RED_SEM_BASE_Notions.

  (* Again a technicality: the plug function is injective. *)
  Lemma elem_plug_injective1 : forall {k1 k2} (ec : elem_context_kinded k1 k2) {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.
  Proof.
    intros ? ? ec t0 t1 H;
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


  Lemma value_trivial1 :
    forall {k1 k2} (ec: elem_context_kinded k1 k2) t,
    forall v : value k1,  ec:[t] = v ->
                        exists (v' : value k2), t = v'.
  Proof with eauto.
    intros ? ? ec t v H;
      dependent destruction ec;
      dependent destruction v; inversion H; subst;
        repeat dep_subst_proof_irrelevance.
    +
      destruct l; try discriminate; simpl in *.
      inversion H1; subst.
      assert (Subset xs0 (x :: xs)).
      unfold Subset in *; intros; eauto.
      case_eq (eq_var x0 x); intros; subst...
      left; auto.
      right.
      apply s.
      eapply set_remove_3; eauto.
      dependent destruction n.
      exists (vStruct _ _ H s0)...
      eexists (vCLam _ _ H l)...
    +
      destruct s0; discriminate.
    +
      dependent destruction n0; try discriminate; inversion H1; subst...
      simpl in *.
      assert (Subset xs1 (x::xs)).
      unfold Subset in *; intros; subst...
      case_eq (eq_var x x0); intros; subst...
      left; auto.
      right; apply s.
      apply set_remove_3...
      assert (~In y (x::xs)).
      intro.
      destruct H0; subst...
      exists (vNeedy _ _ _ H0 H n2)...
    +
      destruct l; try discriminate; inversion H1; subst.
    +
      destruct s0; try discriminate; inversion H1; subst.
      simpl in *.
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; subst...
      apply s.
      apply set_union_intro1...
      exists (vStruct _ _ H s0)...
    +
      dependent destruction n0; try discriminate;
        inversion H1; subst.
      exists (vNeedy _ _ _ n s n1)...
      assert (Subset ys xs)...
      unfold Subset in *; intros; subst...
      apply s.
      apply set_union_intro1...
      exists (vStruct _ _ H s0)...
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
      exists (vStruct _ _ H2 s3)...
      assert (Subset xs1 xs)...
      unfold Subset in *; intros; eauto.
      eapply s1; eauto.
      apply set_union_intro2...
      exists (vCLam _ _ H2 l)...
    +
      dependent destruction n0; try discriminate; inversion H1; subst...
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ H0).
      elim n...
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      simpl in *.
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; eauto.
      eapply s1; eauto.
      apply set_union_intro2...
      exists (vNeedy _ _ _ n H2 n1)...
    +
      destruct s1; discriminate.
    +
      destruct l; try discriminate; inversion H1; subst...
      exists (vCLam _ _ s l)...
    +
      destruct s0; try discriminate; inversion H1; subst.
      exists (vStruct _ _ s s0)...
    +
      destruct n1; try discriminate; inversion H1; subst...
      simpl in *.
      exists (vNeedy _ _ _ n0 s n3)...
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
      exists (vStruct _ _ H s0)...
    +
      destruct s0; try discriminate; inversion H1; subst.
      assert (Subset zs xs)...
      unfold Subset in *; intros; eauto.
      eapply s; eauto.
      apply set_union_intro1...
      exists (vStruct _ _ H s0_1)...
    +
      dependent destruction n0; try discriminate; inversion H1; subst...
      simpl in *.
      assert (Subset xs0 xs)...
      unfold Subset in *; intros; eauto.
      eapply s; eauto.
      apply set_union_intro1...
      exists (vStruct _ _ H s0)...
      exists (vNeedy _ _ _ n s n0)...
    +
      destruct s; try discriminate.
    +
      destruct l; try discriminate; inversion H1; subst...
      simpl in *.
      elim struct_to_term_injective with s0 _ s2; intros; subst...
      assert (Subset xs0 (x :: ys)).
      unfold Subset in *; intros; eauto.
      case_eq (eq_var x0 x); intros; subst; eauto.
      left; auto.
      right; eauto.
      assert (In x0 ys0).
      clear H1 H2 H3 l s2.
      induction i; simpl; eauto.
      elim H0; subst; intros; subst...
      elim n1...
      elim H0; intros; subst...
      right...
      eapply IHi; intros...
      eapply s1...
      destruct (set_union_elim _ _ _ _ H2); intros...
      apply set_union_intro1...
      apply set_union_intro2...
      right...
      inversion n...
      intro.
      elim n0...
      right...
      apply s1...
      apply set_union_intro2...
      exists (vCLam _ _ H0 l)...
    +
      destruct s2; try discriminate; inversion H1; subst.
      elim struct_to_term_injective with s0 _ s2_1; intros; subst...
      assert (Subset xs0 (x :: ys)).
      unfold Subset in *; intros; eauto.
      case_eq (eq_var x0 x); intros; subst; eauto.
      left; auto.
      right; eauto.
      assert (In x0 ys0).
      clear H3 H2 H1 s2_1 s2_2.
      induction i; simpl; eauto.
      elim H0; subst; intros; subst...
      elim n1...
      elim H0; intros; subst...
      right...
      eapply IHi; intros...
      eapply s1...
      destruct (set_union_elim _ _ _ _ H2); intros...
      apply set_union_intro1...
      apply set_union_intro2...
      right...
      inversion n...
      intro.
      elim n0...
      right...
      apply s1...
      apply set_union_intro2...
      exists (vStruct _ _ H0 s2_2)...
    +
      dependent destruction n0; try discriminate; inversion H1; subst...
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
      destruct H3; subst...
      exists (vNeedy _ _ _ H3 H0 n2)...
      assert (hh:=struct_needy_in_vars _ _ _ _ _ _ H2)...
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
    dependent destruction v; intro H; inversion H; dependent destruction s0; try discriminate; try repeat dep_subst_proof_irrelevance.
    +
      destruct l; try discriminate; inversion H1; subst.
    +
      destruct l; try discriminate; inversion H1; subst...
    +
      inversion H1; subst.
    +
      simpl in *.
      inversion H1; subst.
      destruct s0; destruct s1; try discriminate; inversion H0; subst.
      eelim struct_not_sub_lambda...
    +
      destruct s0; try discriminate; inversion H1; subst...
    +
      inversion H1; subst.
    +
      destruct n0; try discriminate; inversion H1; subst.
      inversion H0; subst.
      eelim needy_E_not_sub_lambda with (s0:=subMt) (v:=v1) (r:=t)...
      eelim struct_not_sub_lambda  with (s0:=subMt) (v:=v1) (r:=t)...
    +
      destruct n0; try discriminate; inversion H1; subst.
      dependent destruction n1; try discriminate.
      inversion H0; subst.
      eelim needy_E_not_sub_lambda...
      destruct s1; try discriminate; inversion H0; subst.
      eelim struct_not_sub_lambda...
    +
      destruct s; discriminate.
    +
      destruct s; discriminate.
    +
      dependent destruction v; intro H; inversion H;
      repeat subst_proof_irrelevance.
      - inversion H1; subst.
        dependent destruction l; try discriminate;
        inversion H1; subst...
      - inversion H1; subst.
        destruct s0; try discriminate; inversion H1; subst;
        inversion H1; subst.
        eelim struct_not_sub_lambda...
      - inversion H1; subst.
        dependent destruction n0; try discriminate; inversion H1; subst...
      - dep_subst. destruct s; discriminate.
    +
      dependent destruction v; intro H; inversion H;
      repeat dep_subst_proof_irrelevance.
      - dependent destruction l; try discriminate.
        simpl in *.
        inversion H1; subst.
        assert (hh:=lambda_normal_needy_in_vars _ l _ _ _ n0 H3).
        elim n...
      - destruct s0; try discriminate; inversion H1; subst.
        assert (hh:=struct_needy_in_vars _ _ _ _ _ _ H3)...
      - dependent destruction n0; try discriminate; inversion H1; subst.
        elim (needy_to_term_vars n2 _ _ n3); intros...
      - destruct s; try discriminate; inversion H1; subst.
        eelim needy_E_not_sub_lambda...
    +
      intro H.
      dependent destruction v;
      repeat dep_subst_proof_irrelevance.
      - destruct l; try discriminate.
        inversion H; subst...
      - destruct s0; try discriminate.
        inversion H; subst...
        elim struct_to_term_injective with s0_1 _ s3; intros; subst...
        elim struct_to_term_injective with s0_2 _ s4; intros; subst...
      - destruct n0; simpl in *; try discriminate.
        inversion H; subst...
        inversion H; subst...
      - destruct s; discriminate.
    +
      intro H.
      dependent destruction v;
      repeat dep_subst_proof_irrelevance.
      - destruct l; simpl in *; try discriminate.
        inversion H; subst...
        elim struct_to_term_injective with s3 _ s2; intros; subst...
        elim lambda_normal_to_term_injective with l _ l0; intros; subst...
      - destruct s0; simpl in *; try discriminate.
        inversion H; subst...
      - simpl in *.
        destruct n0; simpl in *; try discriminate.
        inversion H; subst...
        inversion H; subst...
    +
      intro H.
      dependent destruction v; try discriminate;
      repeat dep_subst_proof_irrelevance.
      - destruct s0; try discriminate.
        inversion H; subst...
      - dependent destruction n0; try discriminate.
        inversion H; subst...
        inversion H; subst...
      - destruct s; discriminate.
  Qed.

  (* There are no other potential redices inside a potential redex;
           there can be only values. *)
  Lemma redex_trivial1 :
    forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
      ec:[t] = r -> exists (v : value k'), t = v.
  Proof with eauto.
    intros ? ? r ec t H.
    dependent destruction ec; dependent destruction r;
      subst; repeat dep_subst_proof_irrelevance; inversion H; subst...
    +
      exists (vELam _ _ v  t s)...
    +
      eelim struct_not_sub_lambda...
    +
      exists (vNeedy _ _ _ n0 s n)...
    +
      simpl in *.
      exists (vELam _ _ v t0 s)...
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
  Include RED_STRATEGY_STEP_Notions Lam_cbnd_PreRefSem.


  (* Here is the down-arrow function. *)
  (* It is used to decompose a term.  *)


  Definition dec_term (t : term) k : elem_dec k.
    refine(
        match k with
        | @ckv E xs Hnd => (* decomposition under weak strategy *)
          match t with
          | App t1 t2 => ed_dec _ t1 (□ t2)
          | Var x     =>
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => ed_val (vStruct _ _ _ (sVar x)) (* x is struct *)
            | right p => ed_val (vNeedy _ _ _ _ _ (needyVar x)) (* x is active var in ctx *)
            end
          | Lam x t1  => ed_val (vELam _ _ x t1 subMt) (* lambda - weak value *)
          | Let x t1 t2 => _
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in let *)
              let f := fresh_for xs in
              ed_dec (ckv E Hnd) ([x:=Var f] t2)
                     (k_let _ f _ (fresh_for_is_fresh f xs _) t1)
            | right p => ed_dec (ckv E Hnd) t2 (k_let _ x _ p t1)
            end
          | LetNd x t n => ed_dec _ t (k_definiens _ _ _ n) (* x is needed - decompose t *)
          end
        | @ckv C xs Hnd => (* decomposition under strong strategy *)
          match t with
          | App t1 t2 => ed_dec _ t1 (□ t2)
          | Var x     =>
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => ed_val (vStruct _ _ _ (sVar x)) (* x is struct *)
            | right p => ed_val (vNeedy _ _ _ _ _ (needyVar x)) (* x is active var in ctx *)
            end
          | Lam x t1  =>
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in lam *)
              let f:= fresh_for xs in
              ed_dec _  ([x := Var f] t1) (k_lam_c f _ (fresh_for_is_fresh f xs _))
            | right p => ed_dec _  t1 (λc x, □)
            end
          | Let x t1 t2 =>
            match in_dec eq_var x xs with (* if x is in xs *)
            | left p => (* name clash; need to rename x with fresh var in let *)
              let f:=fresh_for xs in
              ed_dec (ckv C Hnd) ([x:=Var f] t2)
                     (k_let _ f _ (fresh_for_is_fresh f xs _) t1)
            | right p => ed_dec (ckv C Hnd) t2 (k_let _ x _ p t1)
            end
          | LetNd x t n => ed_dec _ t (k_definiens _ _ _ n) (* x is needed - decompose t *)
          end
        end); eauto.
  Defined.



  (* The decomposed term after the decomposition must be equal *)
  (* to itself before the decomposition. *)

  Lemma dec_term_correct : forall t k, t = elem_rec (dec_term t k).
  Proof.
    destruct k,t,c ; simpl; auto;
      case_eq (in_dec eq_var v xs); intros; auto.
    simpl.
    rewrite (α_equiv v (fresh_for xs) (λ v, t)); simpl; auto.
    case_eq (eq_var v v); intros; eauto; elim n0; eauto.
    rewrite (α_equiv v (fresh_for xs) (Let v t1 t2)); simpl; auto.
    case_eq (eq_var v v); intros; eauto; elim n0; eauto.
    rewrite (α_equiv v (fresh_for xs) (Let v t1 t2)); simpl; auto.
    case_eq (eq_var v v); intros; eauto; elim n0; eauto.
  Qed.


  Definition dec_context
     {k k' : ckind} (ec : elem_context_kinded k k') (v : value k') : elem_dec k.
    refine(
        match ec in eck k k' return val k' -> elem_dec k with
        | λc x, □  =>
          fun v =>
            match v in val k' return k' = @ckv C _ _ -> elem_dec _ with
            | vELam _ _ _ _ _  => fun h1 => _ (* absurd case *)
            | @vNeedy C _ y _ _ _ _ c  => (* cʸ *)
              fun h2 =>
                match eq_var x y with
                | left p => ed_dec  _ c (λc x, □)
                | right p => ed_val (vNeedy _ _ _ _ _ (needyLam _ y _ _ c))
                                    (* λ x. cʸ *)
                end
            | @vNeedy E _ _ _ _ _ _ _  => fun h2 => _ (* absurd case *)
            | @vCLam _ _ _ _ l  => (* λ x, l *)
              fun h3 => ed_val (vCLam _ _ _ (lnfLam x _  (nf_lam_in_ctx _ l)))
            | @vStruct E _ _ _ _ _ => fun h4 => _ (* absurd case *)
            | @vStruct C _ _ _ _ s => (* λ x, s *)
              fun h5 => ed_val (vCLam _ _ _ (lnfLam x  _ (nf_struct _ s)))
            end refl_equal
        |  □ t =>
          fun v =>
            match v in val k' return k' = @ckv E _ _ -> elem_dec _ with
            | vELam _ _ x t0 s => (* redex (λ x, t0) [s] @ t *)
              fun h1 => ed_red (@rApp _ _ _ x t0 s t)
            | @vNeedy E _ _ _ _ _ _ c    => (* c @ t *)
              fun h2 => ed_val (vNeedy _ _ _ _ _ (needyApp_l _ _ _ c t))
            | @vNeedy C _ _ _ _ _ _ _    => _ (* absurd case *)
            | vCLam _ _ _ _  => fun _ =>  _ (* absurd case *)
            | @vStruct E _ _ _ _ s =>
              fun h4 => ed_dec _ t (s □)
            | vStruct _ _ _ _ => fun h5 => _ (* absurd case *)
            end refl_equal
        | s □  =>
          fun v => match v in val k' return k' = @ckv C _  _ -> elem_dec _ with
                  | vELam _ _ _  _ _ => fun h6 => _  (* absurd case *)
                  | @vNeedy E _ _ _ _ _ _ _  => _ (* absurd case *)
                  | @vNeedy C _ _ _ _ _  _ c    => (* s @ c *)
                    fun h7 => ed_val (vNeedy _ _ _ _ _ (needyApp_r _ _ _ _ s c))
                  | vCLam _ _ _ l => (* s @ l *)
                    fun h8 => ed_val (vStruct _ _ _ (sApp _ _ s (nf_lam_in_ctx _ l)))
                  | @vStruct C _ _ _ _ s1 => (* s @ s1 *)
                    fun h9 => ed_val (vStruct _ _ _ (sApp _ _ s s1))
                  | vStruct _ _ _ _ => fun h10 => _ (* absurd case *)
                  end refl_equal
        | let_E x = t in □ =>
          fun v =>
            match v in val k return k= @ckv E _ _ -> elem_dec _ with
            | vELam _ _ y r s => (* (Lam y. r) [x=t, s] *)
              fun h11 => ed_val (vELam _ _ y r (subCons x t s))
            | vNeedy y _ _ _ _ c    =>
              fun h12 =>
                match eq_var x y with
                | left _ => ed_red (rSubNd y _ _ _ _ _ ) (* redex let x = t in cˣ *)
                | right _ => ed_val (vNeedy _ _ _ _ _ (needySub _ _ _ _ _ _ t))
                                    (* let x = t in cʸ *)
                end
            | vCLam _ _ _ _  => fun h13 => _ (* absurd case *)
            | @vStruct E _ _ _ _ s => (* let x = t in s *)
              fun h14 => ed_val (vStruct _ _ _ (sSub x _ _ t s))
            | vStruct _ _ _ _ => fun h15 => _ (* absurd case *)
            end refl_equal
        | let_C x = t in □ =>
          fun v =>
            match v in val k return k= @ckv C _  _ -> elem_dec _ with
            | vELam _ y v0 _ s => fun h16 => _ (* absurd case *)
            | vNeedy y _ _ _ _ c    =>
              fun h17 =>
                match eq_var x y with
                | left _ => ed_red (rSubNd y _ _ _ _ t) (* redex let x = t in cˣ *)
                | right _ => ed_val (vNeedy _ _ _ _ _ (needySub x _ _ _ _ _ t))
                                    (* let x = t in cʸ *)
                end
            | vCLam _ _ _ ln  => (* let x = t in ln *)
              fun h18 => ed_val (vCLam _ _ _ (lnfSub _ _ _  t ln))
            | @vStruct E _ _ _ _ s => fun h19 => _ (* absurd case *)
            | vStruct _ _ _ s => (* let x = t in s *)
              fun h20 => ed_val (vStruct _ _ _ (sSub x _ _ t s))
            end refl_equal
        | let k, x:= □ ^ xs in t => (* let x := □ in t *)
          fun v =>
            match v in val k' return k' = @ckv E _ _ -> elem_dec (@ckv k _ _) with
            | vELam _ _ y r s => (* redex let x := (λ y, r)[s] in t *)
              fun h21 => ed_red (rSub x _ t y r s)
            | @vNeedy E _ y _ _ _ _ c    => (* let x := cʸ in t *)
              fun h22 => ed_val (vNeedy y _  _  _ _ (@needyNdSub2 _ y _ x c t))
            | @vNeedy C _ _ _ _ _ _ _    => _ (* absurd case *)
            | vCLam _ _ _ _ => fun h23 => _ (* absurd case *)
            | @vStruct E _ _ _ _ s =>
              fun h24 => _
            (* ed_dec _ t (let2 x := s in □) if x ∉ xs *)
            (* ed_dec _ [x:= #f]t (let2 f := s in □), f - fresh if x ∈ xs *)
            | vStruct _ _ _ _ => fun h25 => _ (* absurd case *)
            end refl_equal
        | let2_C x := s1 in □  => (* let x := s1 in □ *)
          fun v =>
            match v in val k' return k' = @ckv C (x::_) _ -> elem_dec _ with
            | vELam _ y v0 _ s =>  fun h26 => _ (* absurd case *)
            | vNeedy y _ _ _ _ c    => (* let x := s1 in cʸ *)
              fun h27 => ed_val _
                (*ed_val (vNeedy y  _ _ _ _ (needyNdSub _ _ _ _ _ _ s1 _))*)
            | vCLam l _ _ nl =>
              fun h28 => _ (* let x := s1 in nl if x ∈ frozen vars of nl *)
                           (* stuck redex otherwise *)
            | @vStruct E l _ _ _ s => fun h29 => _ (* absurd case *)
            | @vStruct C l _ _ _ s =>
              fun h30 => _ (* let x := s1 in s if x ∈ l *)
                           (* stuck redex otherwise *)
            end refl_equal
        | let2_E x := s1 in □ => (* let x := s1 in □ *)
          fun v =>
            match v in val k' return k' = @ckv E (x::_) _ -> elem_dec _ with
            | vELam _ _ y r s => (* redex let x:= s1 in (Lam y. r)[s] *)
              fun h261 => ed_red (rSubNdE x _ _ _ s1 y r s)
            | @vNeedy _ l y ys _ _ _ c    =>
              fun h271 => ed_val _ (* let x := s1 in cʸ *)
            | vCLam _ _ _ nl => _ (* absurd case *)
            | @vStruct E _ l _ _ s =>
              fun h291 => _ (* let x := s1 in s if x ∈ frozen vars of s*)
                            (* stuck redex otherwise *)
            | @vStruct C _ _ _ _ s => fun h301 => _ (* absurd case *)
            end refl_equal
        end v); try solve [discriminate];
      match goal with
      | [ H : @ckv _ _ _ = @ckv _ _ _ |- _ ] => inversion H; subst; eauto
      | _ => idtac
      end;
      unfold Subset in *; intros; eauto.
   + (* h3 *)
      (*    instantiate (1:=x) in H.*)
     case_eq (eq_var x x0); intros; subst; eauto.
     elim set_remove_2 with _ eq_var x0 x0 s; eauto.
     assert (hh:=set_remove_1 _ _ _ _ H).
     destruct (s0 _ hh); subst; eauto;
       elim n1; auto.
     elim n2; auto.
   + (* h5 *)
     case_eq (eq_var x x0); intros; subst; eauto.
     elim set_remove_2 with _ eq_var x0 x0 s1; eauto.
     assert (hh:=set_remove_1 _ _ _ _ H).
     destruct (s0 _ hh); subst; eauto;
       elim n1; auto.
     elim n2; auto.
   + (* h2 *)
     intro; elim n2; eauto.
     constructor 2; auto.
   + (* h2 *)
     assert (NoDup s) by eauto.
     assert (hh:=set_remove_2 _ H0  H); eauto.
     assert (gh:=set_remove_1 _ _ _ _ H).
      assert (ghh:=s0 _ gh).
      destruct ghh; subst; auto.
      elim hh; eauto.
   + (* h8 *)
     elim (set_union_elim _ _ _ _ H); eauto.
   + (* h9 *)
     elim (set_union_elim _ _ _ _ H); eauto.
   + (* h7 *)
     elim (set_union_elim _ _ _ _ H); eauto.
   + (* h24 *)
     case_eq (@In_split var eq_var x xs); intros; eauto.
     destruct s2 as [x0 [ x1 [a1 a2]]]; subst.
     remember (fresh_for (x0++x::x1)) as f.
     exact (ed_dec _ ([x:=#f]t) (k_letnd f _ _ _ (fresh_for_is_fresh f (x0++x::x1) (eq_sym Heqf)) s0 s)).
     assert (Subset s1 xs) by eauto.
     exact (ed_dec _ t (k_letnd x _ _ _ n1 H0 s)).
    +
      (* h291 *)
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
    + (* h271 *)
      assert (x <> y).
      intro; subst; elim n2; left; eauto.
      assert (~ In y l0).
      intro; elim n2; right; eauto.
      assert (~ In y s) by eauto.
      remember (needyNdSub x y _ _ H H1 s1 c) as val.
      assert (Subset (set_union eq_var s (set_remove eq_var x l)) l0).
      unfold Subset in *; intros; eauto.
      elim (set_union_elim _ _ _ _ H2); intros; eauto.
      assert (hh:=set_remove_1 eq_var _ _ _ H3).
      elim (s2 _ hh); intros; subst; eauto.
      eelim (set_remove_2 _ _ H3); eauto.
      exact (vNeedy y _ _ H0 H2 val).
    + (* h28 *)
      destruct (@In_split var eq_var x s2); eauto.
      assert (NoDup s2) by eauto.
      destruct s4 as [x0 [ x1 [ a1 a2]]]; subst.
      assert (~In x x0) by eauto.
      assert (in_split x (x0 ++ x1) (x0 ++ x :: x1)).
      apply in_split_split; eauto.
      assert (NoDup (x0++x::x1)) by eauto.
      eapply NoDup_remove_1; eauto.
      assert (NoDup (x0 ++ x1))...
      assert (NoDup (x0++x::x1)) by eauto.
      apply NoDup_remove_1 with x; eauto.
      remember (lnfNdSub x (x0++x1) _ _  H1 H2 a2 s1 nl) as vv.
      assert (Subset (set_union eq_var s (x0 ++ x1)) l0).
      unfold Subset in *; intros; subst; eauto.
      assert (hh:=set_union_elim _ _ _ _ H3).
      destruct hh; subst; eauto.
      assert (In x2 (x0 ++ x :: x1)).
      apply in_or_app.
      elim (in_app_or _ _ _ H4); intros; subst; auto.
      right; right; auto.
      assert (gg:=s3 _ H5).
      elim gg; intros; subst; auto.
      elim a2; eauto.
      exact (ed_val (vCLam _ _ H3 vv)).
      (* x ∉ frozen vars of vCLam - stuck term *)
      assert (Subset s2 l0).
      unfold Subset in *; intros; subst.
      assert (hh:=s3 x0 H).
      destruct hh; subst; eauto.
      elim n2; auto.
      assert (Subset s l0) by eauto.
      exact (ed_red (rSubWrong2 x _ _  _ H0 H n2 s1 nl)).
    + (* h30 *)
      assert (NoDup l) by eauto.
      elim (@In_split var eq_var x l H); intros; subst; eauto.
      destruct a as [ x0 [ x1 [ a1 a2]]]; subst.
      assert (in_split x (x0 ++ x1) (x0 ++ x :: x1)) .
      apply in_split_split; eauto.
      eapply NoDup_remove_1; eauto.
      assert (NoDup (x0 ++ x1)) .
      apply NoDup_remove_1 with x; auto.
      remember (sNdSub x (x0++x1) _ _ H0 H1 a2 s1 s) as vv.
      assert (Subset (set_union eq_var s3 (x0 ++ x1)) l0).
      unfold Subset in *; intros; subst; eauto.
      elim (set_union_elim _ _ _ _ H2); intros; subst; eauto.
      elim (in_app_or _ _ _ H3); intros; subst; eauto.
      assert (In x2 (x0 ++ x :: x1)) by eauto.
      elim (s2 _ H5); intros; subst; eauto.
      elim a2; eauto.
      assert (In x2 (x0 ++ x :: x1)).
      apply in_or_app; right; right; auto.
      elim (s2 _ H5); intros; subst; eauto.
      elim a2; eauto.
      exact (ed_val (vStruct _ _ H2 (sNdSub x _ _ _ H0 H1 a2 s1 s))).
      (* x ∉ l *)
      assert (Subset l l0).
      unfold Subset in *; intros; subst; eauto.
      elim (s2 _ H0); intros; subst; eauto.
      elim b; eauto.
      exact (ed_red (rSubWrong x _ _ _ s0 H0 b s1 s)).
    + (* h27 *)
      assert (x <> y).
      intro; subst; elim n2; left; eauto.
      assert (~ In y l).
      intro; elim n2; right; eauto.
      assert (~ In y s) by eauto.
      remember (needyNdSub x y _ _ H H1 s1 c) as val.
      assert (Subset (set_union eq_var s (set_remove eq_var x s2)) l).
      unfold Subset in *; intros; eauto.
      elim (set_union_elim _ _ _ _ H2); intros; eauto.
      assert (hh:=set_remove_1 eq_var _ _ _ H3).
      elim (s3 _ hh); intros; subst; eauto.
      eelim (set_remove_2 _ _ H3); eauto.
      exact (vNeedy y _ _ H0 H2 val).
      Unshelve.
      eauto.
      eauto.
  Defined.


  (* The two pairs (term, context) before and after decomposition represent *)
  (* the same term. *)
  Lemma dec_context_correct : forall {k k'} (ec : elem_context_kinded k k') (v : value k'),
      ec:[v] = elem_rec (dec_context ec v).
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
      rewrite (α_equiv x0 (fresh_for (x++x0::x1)) (LetNd x0 (struct_to_term s0) e)); simpl; auto.
      case_eq (eq_var x0 x0); intros; eauto; elim n0; eauto.
      (* alpha *)
    +
      case_eq (@In_split var eq_var x0 xs Hnd); intros; subst; eauto.
      repeat destruct s1.
      destruct a; subst.
      cbn.
      rewrite (α_equiv x0 (fresh_for (x++x0::x1)) (LetNd x0 (struct_to_term s0) e)); simpl; auto.
      case_eq (eq_var x0 x0); intros; eauto; elim n0; eauto.
      (* alpha *)
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
      repeat destruct s3;
      destruct a...
      subst;
      cbn;
      simpl;
      auto.
  Qed.

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
    | k_letnd _ _ _ _ _ _ _ , k_definiens _ _ _ _=> immediate_ec ec t /\ immediate_ec ec0 t
(*    | k_letnd _ _ _ _ _ _ _ , k_let _ _ _ _ _=> immediate_ec ec t /\ immediate_ec ec0 t
    | k_definiens _ _ _ _ , k_let _ _ _ _ _ => immediate_ec ec t /\ immediate_ec ec0 t *)
    | _, _           => False
    end.


  Ltac prf := dep_subst_proof_irrelevance; try contradiction; try auto.

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
      dep_subst_proof_irrelevance;
      try discriminate;
        try (inversion H; subst; clear H);
        inversion H0; subst; try discriminate;
          inversion H1; simpl in *; try inversion H2; dep_subst;
            (let k0 := fresh k  in
             let ec := fresh ec in
             let H  := fresh H  in
             constructor;
             intros [k0 ec] H;
             dependent destruction ec; dep_subst_proof_irrelevance;
             try discriminate;
             try (inversion H; subst; clear H)).
  Qed.


  (* The search order is transitive. *)
  Lemma search_order_trans :
    forall k t ec0 ec1 ec2,
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 ->
                            k,t |~ ec0 << ec2.
  Proof.
    intros k t [? ec0] [? ec1] [? ec2] H H0.
    destruct ec0; dependent destruction ec1; dep_subst_proof_irrelevance;
      try solve [ autof ].
(*    dependent destruction ec2; prf;
      try solve [ autof ];
    simpl;
    split;
    destruct H; auto.
    destruct H0; auto.*)
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
        dep_subst_proof_irrelevance;
        try discriminate;
        subst;
        inversion H5;
        subst;
        try subst_proof_irrelevance;
             try (elim struct_to_term_injective with s2 _ s0;
                  intros; subst; auto;
                  inversion H5; dep_subst;
                  subst_proof_irrelevance);
             try subst_proof_irrelevance;
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
    destruct ec0; dependent destruction ec1; dep_subst_proof_irrelevance;
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
      try match goal with
      | [ H : _  |~ _ << _  |- _ ] =>
        inversion H; dep_subst
      end;
      try match goal with
      | [ H : match in_dec eq_var ?v ?xs  with  | _ => _ end = _ |- _ ] =>
        case_eq (in_dec eq_var v xs); intros; dep_subst; eauto; rewrite H1 in *; discriminate
      end.
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
          repeat match goal with
          | [ H : match In_split var eq_var ?x0 ?ys ?Hnd0 with
                | _ => _ end _ = _ |- _ ] => let s:=fresh "s" in
                                        case_eq (@In_split var eq_var x0 ys Hnd0); intros s H0;
                                        rewrite H0 in H; clear H0; [destruct s as [s12  [s22 [s32 s42] ] ] | idtac];
                                        dep_subst; try inversion H; subst
          end;
          cbn in H; inversion H; dep_subst;
            intro G;  unfold search_order in G; simpl in G;
              try    destruct G as [ G1 G2 ];
              repeat destruct G1;
              repeat destruct G2; try discriminate;
    try (inversion H0; eelim struct_not_sub_lambda; eauto);
    try (dependent destruction e0 || dependent destruction e1);
      prf; try prf;
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
                  dep_subst_proof_irrelevance;
                    try discriminate;
                    subst;
                    autof
      | [ x0 : var |- _ ] => cbn in H;
               let s:=fresh "s" in
               let h:=fresh "H" in
               case_eq (@In_split _ eq_var x0 xs (struct_NoDup s0 )); intros s h; subst;
                 [ repeat destruct s; destruct a; dep_subst;
                   rewrite h in H;
                   inversion H; subst;
                   rewrite h in H |
                   rewrite h in H;
                   inversion H]
      | _ => try solve [destruct ec; auto]
      | _ => idtac
      end;
      simpl; repeat split; try unfold immediate_ec;
        simpl; try intros; try intro;
          match goal with
          | [ H : match ?ec with | _ => _ end |- _ ]
              => dependent_destruction2 ec;
                   dep_subst_proof_irrelevance;
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
rewrite  (α_equiv x1 (fresh_for (x++x1::x2)) (LetNd x1 (struct_to_term s2) e));
  simpl;
case_eq (eq_var x1 x1); intros; eauto; elim n0; eauto.
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
rewrite  (α_equiv x1 (fresh_for (x++x1::x2)) (LetNd x1 (struct_to_term s2) e));
  simpl;
case_eq (eq_var x1 x1); intros; eauto; elim n0; eauto.
split with t; auto.
split with s0; auto.
Qed.


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


Definition x := Id 1.
Definition z := Id 2.
Definition xx := (λ x, (# x @ # x)).
Definition id := λ  x, # x.
Definition t := xx @ id.
Definition t2 := Let x id (Let (Id 2) (# x) (# (Id 2))).
Definition t3 := Let x id (# x).
Definition t4 := Let x (# z) (# x). (* let x = z in x with empty set of frozen vars is stuck in BB *)
Definition t5 := λ z, Let x (# z) (# x).

Definition t6 :=  Let x (# z) ((# x) @ t).
Definition t7 :=  λ z, Let x (# z) ((# x) @ t).


Definition test := list_configurations t 50.
Definition test1 := list_configurations t3 50.
Definition test4 := list_configurations t4 50.
Definition test5 := list_configurations t5 50.
Definition test6 := list_configurations t6 50.
Definition test7 := list_configurations t7 50.

Eval compute in  test4.


(* Some commands for extraction *)

Set Extraction AccessOpaque.

Extract Inductive nat => int [ "0" "succ"]
"(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant plus => "( + )".

Extraction Inline Lam_cbnd_PreRefSem.value.
Extraction Inline Lam_cbn_Strategy.dec_term.
Extraction Inline Lam_cbn_Strategy.dec_context.
Extraction Inline Lam_cbn_RefSem.dec_term.
Print Extraction Inline.
(*Extraction "eam" Lam_cbn_EAM.dnext_conf.

Extraction "test4" test4.
Extraction "test5" test5.

Extraction "test1" test1.
Extraction "strong_cbn" list_configs .
*)

Unset Extraction SafeImplicits.
Extraction Implicit k_ap_l_E [xs ys].
Extraction Implicit k_let [xs].
Extraction Implicit k_letnd [xs ys].
Extraction Implicit vCLam [xs ys].
Extraction Implicit vStruct [xs ys].
Extraction Implicit vNeedy [xs ys].
Extraction Implicit vELam [xs].
Extraction Implicit needyApp_l [xs].
Extraction Implicit needyApp_r [xs ys].
Extraction Implicit needyLam [xs].
Extraction Implicit needySub [xs].
Extraction Implicit needyNdSub [xs zs].
Extraction Implicit needyNdSub2 [xs].
Extraction Implicit sApp [xs ys].
Extraction Implicit sSub [ys].
Extraction Implicit sNdSub [ys zs xs].
Extraction Implicit lnfLam [xs].
Extraction Implicit lnfSub [ys].
Extraction Implicit lnfNdSub [ys zs xs].
Extraction Implicit nf_struct [xs].
Extraction Implicit nf_lam_in_ctx [xs].
Extraction Implicit struct_to_normal [xs].
Extraction Implicit needy_to_term [xs].
Extraction Implicit rApp [xs].
Extraction Implicit rSub [xs].
Extraction Implicit rSubNd [xs ys].
Extraction Implicit rSubWrong [xs ys zs].
Extraction Implicit rSubWrong2 [xs ys zs].
Extraction Implicit rSubNdE [xs ys].
Extraction Implicit normal_to_term [xs].

(*Extraction "test1_implicit" test1.*)


(* and the complete machine *)
Print Lam_cbn_EAM.

(* extraction relation does not work
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