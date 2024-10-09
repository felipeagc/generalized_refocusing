(* Lambda calculus with the call-by-need reduction strategy *)
(* version of Danvy & Zerny PPDP13, 'revised cbneed λ_let-calculus of Fig. 5 *)

Require Import Program.
Require Import Util.
Require Import refocusing_semantics.
Require Import empty_search_order.
Require Import MSets.

Require Import ListSet.
Require Import Sets.

(* Here we define the reduction semantics. *)
(* The module type PRE_RED_SEM is defined in the file *)
(*     reduction_semantics/reduction_semantics.v *)
(* It is a RED_SEM without totality of decompose *)

Ltac assert_by_proof_irrelevance :=
  match goal with
  | [ H : ?P, H1 : ?P |- _  ] => assert (H=H1) by apply proof_irrelevance
  end.

Ltac subst_proof_irrelevance := assert_by_proof_irrelevance; subst.
Ltac dep_subst_proof_irrelevance := assert_by_proof_irrelevance; dep_subst.


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

  Inductive ck := N.

  Inductive ckvar : Type :=
  | ckv : ck -> var -> ckvar.

  Definition ckind := ckvar.
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

  | ExpSubstS : forall x : var, needy x -> expr -> expr     (* strict explicit substitution n_x[[x / u]] *)
                                                            (* will evaluate u first *)

  | ExpDist   :                                             (* explicit distributor t[x // λy.u] *)
      expr -> var -> var -> expr -> expr                    (* will evaluate t first *)

  | ExpDistS  : forall x : var,                             (* strict explicit distributor n_x[[x // λy.u]] *)
      needy x -> var -> expr -> expr                        (* will evaluate u first *)

  with
    needy : var -> Type := (* needys parameterized by head variable *)
    | nVar       : forall x : var, needy x
    | nApp       : forall x : var, needy x -> expr -> needy x       (* (n_x t) *)

    | nExpSubst  : forall x y,
        x <> y -> needy x -> expr -> needy x (* n_x[y / u] *)
    | nExpSubstS : forall x y,
        needy y -> needy x -> needy x        (* strict n_y[[y / n_x]] *)

    | nExpDist  : forall x y z : var,                               (* n_x[y // λz.u] *)
        x <> y -> needy x -> expr -> needy x.

  Notation " t @ s " := (App t s) (at level 40).
  Notation " # x " := (Var x) (at level 7).
  Notation " t [ x / u ] " := (ExpSubst x u t) (at level 45).
  Notation " t [ x '//' 'λ' y , u ] " := (ExpDist x y u t) (at level 46).
  Notation " 'λ'  x , t " := (Lam x t) (at level 50).

  Definition term := expr.
  Hint Unfold term.


  (* L - Lists context *)
  Inductive ansCtx : ckind -> Type :=
  | ansCtxEmpty : forall {k}, ansCtx k                                  (* <> *)
  | ansCtxSubst : forall {k}, ansCtx k -> var -> term -> ansCtx k         (* L[x / u] *)
  | ansCtxDist  : forall {k}, ansCtx k -> var -> var -> term -> ansCtx k. (* L[x // λy.u] *)

  (* L - Lists context *)
  Inductive sub :=
  | subEmpty : sub                               (* <> *)
  | subSubst : sub -> var -> term -> sub         (* L[x / u] *)
  | subDist  : sub -> var -> var -> term -> sub. (* L[x // λy.u] *)


  Fixpoint sub_to_term (s : sub) (t : term) :=
    match s with
    | subEmpty => t
    | subSubst s' x r => ExpSubst (sub_to_term s' t) x r
    | subDist s' x y r => ExpDist (sub_to_term s' t) x y r
    end.

  (* v *)
  Inductive val : ckind -> Type :=
  | vLam : forall {k}, var -> term -> val k.

  Definition val_to_term {k} (v : val k) : term :=
      match v with
      | vLam x t => Lam x t
      end.

  Coercion val_to_term : val >-> term.

  Inductive answer : ckind -> Type :=
  | ansVal : forall {k}, val k -> sub -> answer k
  | ansNd : forall {k} x, needy x -> answer k.

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
  Fixpoint ansCtx_plug {k} (s : ansCtx k) (t : term) :=
  match s with
  | ansCtxEmpty => t
  | ansCtxSubst s' x r => ExpSubst (ansCtx_plug s' t) x r
  | ansCtxDist s' x y r => ExpDist (ansCtx_plug s' t) x y r
  end.

  Fixpoint sub_to_ansCtx {k} (s : sub) : ansCtx k :=
    match s with
    | subEmpty => ansCtxEmpty
    | subSubst s' x r => ansCtxSubst (sub_to_ansCtx s') x r
    | subDist s' x y r => ansCtxDist (sub_to_ansCtx s') x y r
    end.


  Fixpoint needy_to_term {x} (n : needy x) : term :=
  match n with
  | nVar x => Var x
  | nApp _ n t => App (needy_to_term n) t
  | nExpSubst _ y _ n e => ExpSubst (needy_to_term n) y e
  | nExpSubstS _ y n_y n_x => ExpSubstS y n_y (needy_to_term n_x)

  | nExpDist _ y z _ n_x e => ExpDist (needy_to_term n_x) y z e
  end.


  Definition answer_to_term {k} (a : answer k) : term :=
  match a with
  | ansVal v s => sub_to_term s v
  | ansNd _ n   => needy_to_term n
  end.

  Coercion answer_to_term : answer >-> term.
  Coercion needy_to_term : needy >-> term.

  (* Here we define the set of potential redices. *)
  (* Actually, they are just redices as defined in the paper *)
  (* Inductive red : ckind -> Type := *)
  (* | rApp  : forall {k} {n:nat}, ansCtx k -> val k -> term -> red k        (1* L<v> u *1) *)
  (* | rSplS : forall {k} (n:nat) x, needy x -> val k -> ansCtx k -> red k   (1* N<<x>>[[x/L<λy.p>]] *1) *)
  (* | rSpl  : forall {k} {n:nat} x, needy x -> term -> red k                (1* N<<x>>[x/t] *1) *)
  (* | rLsS  : forall {k} {n:nat} x, needy x -> val k -> red k               (1* N<<x>>[[x//v]] *1) *)
  (* | rLs   : forall {k} {n:nat} x, needy x -> val k -> red k.              (1* N<<x>>[x//t] *1) *)




(* Here we define the set of potential redices. *)
 (* Actually, they are just redices as defined in the paper *)
 Inductive red : ckind -> Type :=
 | rApp  : forall {k}, val k -> sub -> term -> red k (* L<λx.u> t *)
 | rSplS : forall {k} x, needy x -> val k -> sub -> red k (* N<<x>>[[x/L<λy.p>]] *)
 | rSpl  : forall {k} x, needy x -> term -> red k                (* N<<x>>[x/t] *)
 | rLsS  : forall {k} x, needy x -> val k -> red k               (* N<<x>>[[x//v]] *)
 | rLs   : forall {k} x, needy x -> val k -> red k.              (* N<<x>>[x//v] *)
 (* TODO  check "val k" vs. "val (ckv k z)". the same for ansCtx *)

  (* Daniel: redices for `activations':
      + N<<x>>[x/t]  -> N<<x>>[[x/t]]
      + N<<x>>[x//t] -> N<<x>>[[x//t]]
   *)

  Definition redex := red.
  Hint Unfold redex.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp v l t => App (sub_to_term l (val_to_term v)) t
      | rSplS x n v s => ExpSubstS x n (sub_to_term s (val_to_term v))
      | rSpl x n t => ExpSubst (needy_to_term n) x t
      | rLsS x n (vLam y t) => ExpDistS x n y t
      | rLs x n (vLam y t) => ExpDist (needy_to_term n) x y t
      end.

  Coercion redex_to_term : redex >-> term.

  (* This again is a required axiom in the signature of RED_SEM module *)
  Lemma val_to_term_injective :
      forall {k} (v v' : val k), val_to_term v = val_to_term v' -> v = v'.
  Proof with eauto.
    destruct v. intros. dependent destruction v'. inversion H.
    reflexivity.
  Qed.


  Lemma ansCtx_plug_val_injective :
    forall {k} (s s' : ansCtx k) (v v' : val k),
    ansCtx_plug s v = ansCtx_plug s' v' -> s = s' /\ v = v'.
  Proof with auto.
    intros k s s' v v' H.
    induction s; dependent destruction s'; inversion H.
    destruct v; dependent destruction v'; inversion H1...
    destruct v0; dependent destruction s'; inversion H1...
    destruct v1; dependent destruction s'; inversion H1...
    destruct v; dependent destruction v'; inversion H1...
    split; f_equal; elim IHs with s' v1 v'...
    dependent destruction s; destruct v'; inversion H1; split...
    split; f_equal; elim IHs with s' v3 v'...
  Qed.


  Lemma ansCtx_plug_var_injective :
    forall {k} (s s' : ansCtx k) x x',
    ansCtx_plug s (Var x) = ansCtx_plug s' (Var x') -> s = s' /\ x = x'.
  Proof with auto.
    intros k s s' x x' H.
    induction s; dependent destruction s'; inversion H...
    split; f_equal; elim IHs with s'...
    split; f_equal; elim IHs with s'...
  Qed.


  Lemma ansCtx_plug_needy :
    forall {k} (s s' : ansCtx k) (v : val k) {x} (n : needy x),
    ansCtx_plug s v = ansCtx_plug s' n -> False.
  Proof with auto.
    induction s; simpl; intros.
    destruct v; destruct s'; destruct n; discriminate.
    destruct s'. destruct n; simpl in *; try discriminate.
    inversion H; elim IHs with ansCtxEmpty v0 x n0...
    inversion H; elim (IHs _ _ _ _ H1).
    inversion H.
    destruct s'. destruct n; simpl in *; try discriminate.
    inversion H. elim IHs with ansCtxEmpty v1 x n0...
    inversion H; elim (IHs _ _ _ _ H1).
    inversion H; elim (IHs _ _ _ _ H1).
  Qed.

  Lemma ansCtx_plug_var :
    forall {k} (s s' : ansCtx k) x (v : val k),
    ansCtx_plug s v = ansCtx_plug s' (Var x) -> False.
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
    - dependent rewrite H0...
    - subst; rewrite proof_irrelevance with (x0 <> y) n n1...
    - dependent rewrite H2. elim IHn2 with n'2; intros; subst...
      dependent rewrite H0; auto.
    - elim IHn2 with n'2...
    - subst; rewrite proof_irrelevance with (x0 <> y) n n1...
 Qed.


Lemma sub_to_term_val_injective :
    forall {k} (s s' : sub) (v v' : val k),
      sub_to_term s v = sub_to_term s' v' ->
      s = s' /\ v = v'.
  Proof with eauto.
    intros k s.
    induction s; intros; dependent destruction s'; inversion H.
    destruct v; dependent destruction v'; inversion H...
    destruct v0; dependent destruction s'; inversion H...
    destruct v1; dependent destruction s'; inversion H...
    destruct v0; dependent destruction v'; inversion H...
    elim IHs with s' v1 v'; intros; subst...
    destruct v1; dependent destruction v'; inversion H...
    elim IHs with s' v3 v'; intros; subst...
 Qed.

Lemma sub_to_term_var_injective :
    forall (s s' : sub) x x',
      sub_to_term s (Var x) = sub_to_term s' (Var x') -> s = s' /\ x = x'.
  Proof with eauto.
    intros s.
    induction s; intros; dependent destruction s'; inversion H...
    elim IHs with s' x x'; intros; subst...
    elim IHs with s' x x'; intros; subst...
  Qed.

(*DANIEL: based on strong lemmas *)
  Lemma answer_val_not_needy :
  forall {k} (s: sub) (v : val k) t,
      sub_to_term s v = t ->
      forall {x} (n : needy x), t = needy_to_term n ->   False.
  Proof.
   induction s; intros; dependent destruction v;
   dependent destruction n; subst; try discriminate.
  Admitted.

  Lemma answer_to_term_injective :
    forall {k} (a a' : answer k),
    answer_to_term a = answer_to_term a' -> a = a'.
  Proof with auto.
   dependent destruction a; dependent destruction  a'; intros; inversion H;
      subst; repeat dep_subst_proof_irrelevance.
    - f_equal; elim sub_to_term_val_injective with s s0 v v0...
    - eelim answer_val_not_needy; eauto.
    - eelim answer_val_not_needy; eauto.
    - elim needy_to_term_injective with n n0; intros; subst...
      rewrite H...
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
    destruct r; dependent destruction r';
    inversion H; subst.
    - eelim sub_to_term_val_injective; intros; eauto; subst; trivial.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - eelim sub_to_term_val_injective; intros; eauto; subst; trivial.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - f_equal; elim needy_to_term_injective with n n0; intros; subst...
    - dependent destruction v... inversion H.
    - dependent destruction v... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
      reflexivity.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v... inversion H.
    - dependent destruction v; dependent destruction v0... inversion H.
    - dependent destruction v; dependent destruction v0;
      elim needy_to_term_injective with n n0; intros; subst; inversion H...
      rewrite <- H0; reflexivity.
  Qed.


  (* Here comes the actual definition of the grammar of contexts. *)
  (* We have two three non-trivial productions:  E -> E t,  E -> let x = t in E and *)
  (* E -> let x := E in E[x] *)
  (* There is also a trivial production  E -> [] which is omitted here. *)
  (* The first parameter of eck is the nonterminal on the left-hand side; *)
  (* the second parameter is the kind of the hole, i.e., the (unique) nonterminal *)
  (* occurring on the right-hand side of a production. *)


  (* N *)
  Inductive eck : ckind -> ckind -> Type :=
  | eckApp : forall {m n}, term -> eck (ckv N m) (ckv N n)                   (* N -> N t *)
  | eckSubst : forall {m n}, var -> term -> eck (ckv N m) (ckv N n)          (* N -> N[x / t] *)
  | eckDist : forall {m n}, var -> var -> term -> eck (ckv N m) (ckv N n)    (* N -> N[x // λy.u] *)
  | eckPlugSubst : forall {m n} x, needy x -> eck (ckv N m) (ckv N n).       (* N -> N<<x>>[x/N] *)

  Definition elem_context_kinded := eck.
  Hint Unfold elem_context_kinded.

  (* The starting symbol in the grammar *)
  Definition init_ckind : ckind     :=  ckv N (Id 0).

  (* The function for plugging a term into an elementary context *)
  Definition elem_plug {k1 k2} (t : term) (ec : elem_context_kinded k1 k2) : term :=
      match ec with
      | eckApp t' => App t t'
      | eckSubst x s => ExpSubst t x s
      | eckDist x y u => ExpDist t x y u
      | eckPlugSubst x n => ExpSubstS x n t
      end.


  (* Here we define substitution used in the definition of contraction. *)

  (* substitute term s for the needed variable x in the needy term n *)
  Fixpoint subst_needy (x : var) (n : needy x) (s : term) : term :=
    match n with
    | nVar x' => s                                 (* [x][x:=s] = s *)
                                                   (* types guarantee that x'=x *)
    | nApp x' n t => App (subst_needy x' n s) t    (* (n[x] t)[x:=s] = (n[s] t) *)
                                                   (*  again, types guarantee that x'=x *)
    | nExpSubst x' y _ n t => ExpSubst (subst_needy x' n s) y t
    | nExpSubstS x' y ny nx => ExpSubstS y ny (subst_needy x' nx s)

    | nExpDist x' y z _ nx t => ExpDist (subst_needy x' nx s) y z t
    end.


  (* Now we are ready to define the contraction. *)
  (* For the sake of simplicity we do not introduce the fourth (derived) rule *)

  (*
     Declares a set of nats using Coq.MSets.MSets.
     Later this should be converted to a set of vars.
   *)
  Module S := Make Nat_as_OT.

  Fixpoint fvn {x} (t : needy x) : S.t :=
    match t with
    | nVar (Id x) => S.singleton x
    | nApp _ p q => S.union (fvn p) (fv q)
    | nExpSubst (Id x) (Id y) _ nx u => S.union (S.remove y (fvn nx)) (fv u)
    | nExpSubstS (Id x) (Id y) nx ny => S.union (S.remove y (fvn ny)) (fvn nx)
    | nExpDist (Id x) (Id y) (Id z) _ nx u => S.union (S.remove y (fvn nx)) (S.remove z (fv u))
    end
  with fv (t : term) : S.t :=
    match t with
    | Var (Id x) => S.singleton x
    | Lam (Id x) p => S.remove x (fv p)
    | App p q => S.union (fv p) (fv q)
    | ExpSubst t (Id x) u => S.union (S.remove x (fv t)) (fv u)
    | ExpSubstS (Id x) nx u => S.union (S.remove x (fvn nx)) (fv u)
    | ExpDist t (Id x) (Id y) u => S.union (S.remove x (fv t)) (S.remove y (fv u))
    | ExpDistS (Id x) nx (Id y) u => S.union (S.remove x (fvn nx)) (S.remove y (fv u))
    end.

  Fixpoint concat_sub (l1 : sub) (l2 : sub) : sub :=
    match l1 with
    | subEmpty => l2
    | subSubst l1 v t => subSubst (concat_sub l1 l2) v t
    | subDist l1 x y u => subDist (concat_sub l1 l2) x y u
    end.

  (* Fixpoint fresh_var (t : term) : nat := *)
  (*   match t with *)
  (*   | Var (Id x) => x *)
  (*   | Lam (Id x) p => max (fresh_var p) x *)
  (*   | App p q => max (fresh_var p) (fresh_var q) *)
  (*   | ExpSubst p (Id x) u => max (max (fresh_var p) (fresh_var u)) x *)
  (*   | ExpSubstS (Id x) nx u => max (max (fresh_var u) (fresh_var (needy_to_term  nx))) x *)
  (*   | ExpDist p (Id x) (Id y) u => max (max (max (fresh_var p) (fresh_var u)) y) x *)
  (*   | ExpDistS (Id x) nx (Id y) u => max (max (max (fresh_var (needy_to_term nx)) (fresh_var u)) y) x *)
  (*   end. *)

  Fixpoint fresh_ind_n {x} (nx : needy x) : nat :=
    match nx with
    | nVar (Id x) => x
    | nApp _ nx t => max (fresh_ind_n nx) (fresh_ind t)
    | nExpSubst (Id x) (Id y) _ nx u => max (max (max (fresh_ind_n nx) (fresh_ind u)) y) x
    | nExpSubstS (Id x) (Id y) nx ny => max (max (max (fresh_ind_n nx) (fresh_ind_n ny)) y) x
    | nExpDist (Id x) (Id y) (Id z) _ nx u => max (max (max (max (fresh_ind_n nx) (fresh_ind u)) z) y) x
    end
  with fresh_ind (t : term) : nat :=
    match t with
    | Var (Id x) => x
    | Lam (Id x) p => max (fresh_ind p) x
    | App p q => max (fresh_ind p) (fresh_ind q)
    | ExpSubst p (Id x) u => max (max (fresh_ind p) (fresh_ind u)) x
    | ExpSubstS (Id x) nx u => max (max (fresh_ind u) (fresh_ind_n nx)) x
    | ExpDist p (Id x) (Id y) u =>
        max (max (fresh_ind p) (fresh_ind u)) (max x y)
    | ExpDistS (Id x) nx (Id y) u =>
        max (max (fresh_ind_n nx) (fresh_ind u)) (max x y)
    end.

  Fixpoint skl_extract (t : term) (theta : S.t) (n : nat) : sub * term * nat :=
    if S.is_empty (S.inter theta (fv t)) then
      let x := Id n in
      (subSubst subEmpty x t, Var x, n+1)
    else match t with
         | Var x =>
             (subEmpty, Var x, n)
         | Lam (Id x) t =>
             let '(l, t', v) := skl_extract t (S.add x theta) n in
             (l, Lam (Id x) t', n)
         | App p q =>
             let '(l1, p', v) := skl_extract p theta n in
             let '(l2, q', v) := skl_extract q theta n in
             (concat_sub l1 l2, App p' q', n)
         | ExpSubst p (Id x) u =>
             let '(l1, p', n') := skl_extract p (S.add x theta) n in
             let '(l2, u', m) := skl_extract u theta n' in
             (concat_sub l2 l1, ExpSubst p' (Id x) u', m)
         (*DANIEL: extraction not acting on needy terms *)
         | ExpSubstS (Id x) nx u =>
             let '(l1, u', m) := skl_extract u theta n in
             (l1, ExpSubstS (Id x) nx u', m)
         | ExpDist p (Id x) (Id y) u =>
             let '(l1, p', n') := skl_extract p (S.add x theta) n in
             let '(l2, u', m) := skl_extract u (S.add y theta) n' in
             (concat_sub l2 l1, ExpDist p' (Id x) (Id y) u', m)
         (*DANIEL: extraction not acting on needy terms *)
         | ExpDistS (Id x) nx (Id y) u =>
             let '(l1, u', m) := skl_extract u (S.add y theta) n in
             (l1, ExpDistS (Id x) nx (Id y) u', m)
         end.

  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp (vLam x t) l u => Some (ansCtx_plug (@sub_to_ansCtx k l) (ExpSubst t x u))
      | rSplS x nx (vLam (Id y) t) l =>
          match k with
          | @ckv _ (Id n) =>
               let '(l', p', _) := skl_extract t (S.singleton y) n in
               Some (sub_to_term l (sub_to_term l' (ExpDistS x nx (Id y) p')))
          end
      | rSpl x nx t => Some (ExpSubstS x nx t)
      | rLsS x nx (vLam y p) => Some (ExpDist (subst_needy x nx (@vLam k y p)) x y p)
      | rLs x nx (vLam y p) => Some (ExpDistS x nx y p)
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
    destruct ec; dependent destruction v; inversion H.
    - try (dependent destruction s;
      dependent destruction v; discriminate).
    - destruct n0; try discriminate.
      exists (ansNd x n0); inversion H; subst...
    - dependent destruction s; dependent destruction v; try discriminate.
      injection H1; intros; subst...
      exists (ansVal (vLam v t1) s)...
    - destruct n0; try discriminate.
      injection H; intros; subst;
      exists (ansNd _ n1); simpl; auto.
    - dependent destruction s; dependent destruction v; try discriminate.
      injection H1; intros; subst...
      exists (ansVal (vLam v t1) s)...
    - destruct n0; try discriminate.
      injection H; intros; subst;
      exists (ansNd _ n1); simpl; auto.
    - dependent destruction s; dependent destruction v; try discriminate.
    - destruct n1; try discriminate.
      inversion H1; subst...
      exists (ansNd _ n1_2)...
  Qed.


  (* A value is not a redex. *)

  Lemma value_redex : forall {k} (v : value k) (r : redex k),
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    intros k v r.
    destruct r; destruct v; intro H; inversion H;
    try (dependent destruction a0;
    dependent destruction v; try discriminate).
    - dependent destruction s0;
      inversion H; intros; subst...
      + dependent destruction v. dependent destruction v0. discriminate.
    - destruct n; inversion H1; subst;
      elim lCtx_plug_needy with l lEmpty v0 x n...
    - dependent destruction l0;
      inversion H; intros; subst...
      + dependent destruction v. dependent destruction v0. discriminate.
    - destruct n0; try discriminate; inversion H; intros; subst.
      elim lCtx_plug_needy with l lEmpty v0 _ n0_2...
    - dependent destruction l;
      inversion H1; intros; subst...
      + dependent destruction v. discriminate.
      + elim lCtx_plug_needy with l lEmpty v _ n...
    - destruct n0; try discriminate.
      inversion H1; subst.
      elim needy_to_term_injective with n1 n...
    - dependent destruction l;
      inversion H1; intros; subst...
      + dependent destruction v; dependent destruction v0; discriminate.
      + dependent destruction v; dependent destruction v1; discriminate.
      + dependent destruction v; dependent destruction v2; discriminate.
    - dependent destruction v0; destruct n0; discriminate.
    - dependent destruction l;
      inversion H1; intros; subst...
      + dependent destruction v; dependent destruction v0; discriminate.
      + dependent destruction v; dependent destruction v1; discriminate.
      + dependent destruction v. dependent destruction v2.
        inversion H.
        elim lCtx_plug_needy with l lEmpty (vLam v p) _ n...
    - dependent destruction v0.
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
    - exists (ansVal v l)...
    - dependent destruction v.
  Admitted.
      (* exists (ansNd x n). *)
    (* - exists (ansVal v l)... *)
      (* exists (ansNd x n). *)
    (* - exists (ansNd _ n)... *)
    (* exists (ansVal v l)... *)
  (* Qed. *)

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

