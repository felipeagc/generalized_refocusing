(* 
* Language with small step reduction
* no reduction in the empty context 
* full normalization
*)

Require Import Program
               Util
               refocusing_semantics.



Module Lam_NO_CC_PreRefSem <: PRE_REF_SEM.

  Parameter var : Set.
  Parameter kvar : Set.

  Inductive ck := Eᵏ | Fᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.

  Inductive expr : Type :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr
  | Throw : kvar -> expr -> expr
  | Callcc : kvar -> expr -> expr.

  Definition term := expr.
  Hint Unfold term.


Inductive  val : ckind -> Type :=
  | vELam : var -> val Eᵏ -> val Eᵏ
  | vVar : forall {k}, var -> val k
  | vApp : forall {k}, valA -> val Eᵏ -> val k
  | vFLam : var -> term -> val Fᵏ
  | vThrow : kvar -> val Eᵏ -> val Eᵏ
  | vFThrow : kvar -> term -> val Fᵏ
  | vECC : kvar -> val Eᵏ -> val Eᵏ 
  | vFCC : kvar -> term -> val Fᵏ 

with valA : Type :=

  | vAVar : var -> valA
(*  | vAThrow : kvar -> val Eᵏ -> valA*)
  | vAApp : valA -> val Eᵏ -> valA
.

  Definition value := val.
  Hint Unfold value.

  Scheme 
   val_Ind   := Induction for val Sort Prop
with 
   valCa_Ind := Induction for valA Sort Prop.

Inductive eck : ckind -> ckind -> Type :=
  | k_lam_c : var -> eck Eᵏ Eᵏ
  | k_ap_r : forall {k}, expr -> eck k Fᵏ
  | k_ap_l : forall {k}, valA -> eck k Eᵏ
  | k_cc : kvar -> eck Eᵏ Eᵏ
  | k_throw : kvar -> eck Eᵏ Eᵏ.


  Definition elem_context_kinded := eck.

Inductive context (k : ckind) : ckind -> Set :=
| empty : context k k
| ccons : forall {k2 k3} {ec : elem_context_kinded k2 k3}, context k k2 -> context k k3.


  Arguments empty {k}. Arguments ccons {k} {k2} {k3} _ _.

  Notation "[.]"      := empty .
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).


  Inductive ec :=
  | lam_c : var -> ec
  | ap_r  : term -> ec
  | ap_l  : valA -> ec
  | cc : kvar -> ec
  | throw : kvar -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Inductive red : ckind -> Type :=
  | rApp : forall {k}, var -> term -> term -> red k
  | rCC : kvar -> term -> forall {k}, eck k Fᵏ -> red k
  | rThrow : forall {k}, kvar -> term -> eck Fᵏ Fᵏ -> red k.
(*  | rCCMT : forall {k}, var -> term -> red k.*)

  Definition redex := red.
  Hint Unfold redex.

  Definition init_ckind : ckind     :=  Eᵏ.

  Hint Unfold init_ckind.



  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vELam x v => Lam x (value_to_term v)
      | vVar x => Var x
      | vApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      | vFLam x t => Lam x t
(*      | vFCtx k t => Ctx k t*)
      | vThrow k v => Throw k (value_to_term v)
      | vFThrow k t => Throw k t
      | vFCC k t => Callcc k t
      | vECC k v => Callcc k (value_to_term v) 
      end

  with valA_to_term v : term :=
      match v with
      | vAVar x => Var x
      | vAApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valA_to_term  : valA >-> term.


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v'); auto;
    dependent destruction v';
 intro H; inversion H; f_equal...
(*simpl in *.
dependent_destruction2 v1; try discriminate; eauto...
simpl in *; auto.
dependent_destruction2 v0; try discriminate; eauto...
simpl in *.
injection H; intros; subst; simpl; auto.*)
(*subst; assert (hh:=inj_pair2 _ _ _ _ _ H2).
elim (inj_pair2 _ _ _ _ _ hh)...
subst; assert (hh:=inj_pair2 _ _ _ _ _ H2).
elim (inj_pair2 _ _ _ _ _ hh)...
*)
  Qed.


  Lemma valA_to_term_injective :
      forall v v', valA_to_term v = valA_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v'); auto;
    dependent destruction v'; intro H; inversion H; f_equal...
(*subst; assert (hh:=inj_pair2 _ _ _ _ _ H2).
elim (inj_pair2 _ _ _ _ _ hh)...
subst; assert (hh:=inj_pair2 _ _ _ _ _ H2).
elim (inj_pair2 _ _ _ _ _ hh)...
*)
  Qed.





Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} :
                       context k3 k1 -> context k3 k2:=
fun c1 =>
match c0 with
| @empty _=> c1
| ec0 =: c2 => ec0 =: compose c2 c1
end.


  Infix "~+" := compose (at level 60, right associativity).

(*
  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).
*)

 Definition erase_kinds : forall {k1 k2} (e : elem_context_kinded k1 k2), elem_context :=
  fun k1 k2 e => 
  match e with
  | k_lam_c x => lam_c x
  | k_ap_r t => ap_r t 
  | k_ap_l a => ap_l a
  | k_cc k => cc k
  | k_throw k => throw k
  end.


  Coercion erase_kinds : elem_context_kinded >-> elem_context.

  Definition elem_plug (t : term) (ec : elem_context) : term :=
      match ec with
      | lam_c x => Lam x t
      | ap_r tr => App t tr
      | ap_l v  => App (v : term) t
      | cc k => Callcc k t 
      | throw k => Throw k t
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Lemma elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ec t0 t1 H.
    destruct ec;
    solve [ injection H; trivial ].
  Qed.

  
  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug (erase_kinds ec):[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t.

  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp x t1 t2   => App (Lam x t1) t2
      | rCC k t ec => (erase_kinds ec):[Callcc k t]
      | rThrow k t ec => (erase_kinds ec):[Throw k t]
(*      | rCCMT k t => Callcc k t*)
      end.
  Coercion redex_to_term : redex >-> term.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.

dependent destruction r; dependent destruction r'; inversion H; f_equal; auto;
dependent destruction e; try dependent destruction e0; try discriminate;
injection H1; intros; subst; auto.

Qed.



  Parameter subst : var -> term -> term -> term.
  Parameter subst_k : kvar -> term -> elem_context -> term.
 
Definition contract0 {k} (r : redex k) : option term :=
      match r in red k with
      | rApp x t0 t1 => Some (subst x t1 t0)
      | rCC k0 t ec => match k return option term with
                                    | Fᵏ =>Some (Callcc k0 ((erase_kinds ec):[subst_k k0 t (erase_kinds ec)]))
                                    | _ => None
                                    end
      | rThrow k0 t ec => match k return option term with
                                         | Fᵏ => Some (Throw k0 t)
                                         | _ => None
                                         end
(*       | rCCMT k0 t => Some (subst_mt k0 t)*)
      end.

  Definition contract {k} (r : redex k) := contract0 r.



  Lemma valA_is_valF : 
      forall v1 : valA, exists v2 : value Fᵏ, valA_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vVar v)...
     - exists (vApp v1 v)...
  Qed.

(*
Lemma valE_is_valF :
  forall vE : val Eᵏ, exists vF : value Fᵏ, value_to_term vE = value_to_term vF.
Proof with auto using valA_is_valF.
intro vE; dependent induction vE...
- exists (vFLam v (value_to_term vE))...
- exists (vVar v)...
- exists (vApp v vE)...
- simpl.
exists (vFThrow k (value_to_term vE))...
- edestruct (IHvE vE)...
exists (vFCC k x)...
simpl.
rewrite H.
auto.
Qed.
*)
  Lemma value_trivial1 :
  forall {k1 k2} (ec:elem_context_kinded k1 k2) {t},
       forall v : value k1,  ec:[t] = v -> 
           exists (v' : value k2), t = v'.
  Proof with auto.
    intros k1 k2 ec t v H.
    dependent destruction ec.
    dependent destruction v0;
    inversion H; subst; eautof.
    dependent destruction v;
    inversion H; subst; auto using valA_is_valF.
    dependent destruction v0;
    inversion H; subst...
    eauto.
    simpl in *.
dependent_destruction2 v; try discriminate.
simpl in *.
injection H; intros; subst.
eexists H0...
simpl in *.
  dependent destruction v; inversion H; subst; eauto.

  Qed.


  Lemma redex_trivial1 : forall {k k'} (r : redex k) (ec : elem_context_kinded k k') t,
                             ec:[t] = r -> 
                                 exists (v : value k'), t = v.
  Proof with auto.
    intros k k' r ec t H0.

    generalize dependent r.
    dependent destruction ec; intros; dependent destruction r; inversion H0; subst;
    try solve 
    [ eexists (vFLam _ _); reflexivity
    | eauto using valA_is_valF
    | destruct v; inversion H1 ].

dependent_destruction2 e; discriminate.
simpl in *.

dependent destruction e; try discriminate.
simpl in*.
dependent_destruction2 e0; try discriminate.
simpl in *.
exists (vFCC k t0);  dependent destruction e; intros; inversion H0; subst; auto.
simpl in *.
dependent_destruction2 e0; try discriminate.
simpl in *.
eexists (vFThrow k0 t0).
injection H0; intros; subst...

dependent destruction e; try discriminate.
simpl in *.
injection H0; intros; subst...
dependent_destruction2 v; discriminate.
simpl in *.

dependent destruction e; dependent_destruction2 v; discriminate.
dependent destruction e; discriminate.
dependent_destruction2 e; discriminate.
dependent_destruction2 e; discriminate.
dependent_destruction2 e; discriminate.
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (valA_to_term ?v) _ <> _ => dependent_destruction2 v
    end;
try dependent_destruction2 e;
    solve [ discriminate ].
  Qed.

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


  Definition dec (t : term) k (d : decomp k) : Prop := 
      t = d.


  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].

  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End Lam_NO_CC_PreRefSem.




Module Lam_NO_CC_Strategy <: REF_STRATEGY Lam_NO_CC_PreRefSem.

  Import Lam_NO_CC_PreRefSem.


  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : forall {k'}, term -> elem_context_kinded k k' -> interm_dec k
  | in_val  : value k -> interm_dec k.
  
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k k'} _ _.

  Definition dec_term t k : interm_dec k :=

      match k as k0 return interm_dec k0 with 
      | Eᵏ   => match t with
                | App t1 t2 => in_term t1 (k_ap_r t2)
                | Var x     => in_val (vVar x)
                | Lam x t1  => in_term t1 (k_lam_c x)
                | Throw k t => in_term t (k_throw k)
                | Callcc k t => in_term t (k_cc k) 
                  end
      | Fᵏ   => match t with
                | App t1 t2 => in_term t1 (k_ap_r t2)
                | Var x     => in_val (vVar x)
                | Lam x t1  => in_val (vFLam x t1)
                | Throw k t => in_val (vFThrow k t)
                | Callcc k t => in_val (vFCC k t)
                end
       end.

Require Import Program.
(*
Definition dec_context0 k k' (ec : elem_context_kinded k k') (v : value k') : interm_dec k.

dependent destruction ec; subst; intros.
exact (in_val (vELam v v0)).
dependent destruction v.
exact (in_term e (k_ap_l (vAVar v))).
exact (in_term e (k_ap_l (vAApp v v0))).
exact (in_red (rApp v t e)).
exact (in_red (rCC k0 t (k_ap_r e))).
exact (in_val (vApp v v0)). 
exact (in_val (vECC v v0)).
Defined.
*)

(*
Definition dec_context :=dec_context0.
*)


Program Definition dec_context k k' (ec : elem_context_kinded k k') :
value k' -> interm_dec k:=
fun v : value k' =>
      match ec in eck k k' return val k' -> interm_dec k with

      | k_lam_c x  => fun v => in_val (vELam x v)

      | @k_ap_r  k t  => fun v : val Fᵏ  => 
match v in val k'  return k' = Fᵏ  -> interm_dec k with
| vVar x => fun _ => (in_term t (k_ap_l  (vAVar x)))         
| vApp v1 v2 => fun _ => (in_term t (k_ap_l (vAApp v1 v2)))
| vFLam x t0 => fun _ => in_red (rApp x t0 t)
| vThrow k0 v => _
| vFThrow k0 t0 => fun _ => in_red (rThrow k0 t0 (k_ap_r t))
| vFCC k0 t0 => fun _ => in_red (rCC k0 t0 (k_ap_r t))
| vECC k0 v0 => fun Heq => _
| vELam x v0 => fun Heq => _
end (refl_equal) 

      | k_ap_l v0  => fun v : val Eᵏ => in_val (vApp v0 v)
      | k_throw k => fun v : val Eᵏ => in_val (vThrow k v) 
      | k_cc k0 => fun v : val Eᵏ => in_val (vECC k0 v)
     end v.

  Lemma dec_term_correct : 
      forall (t : term) k, match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
       end.

  Proof.
    destruct k, t; simpl; 
    auto.
  Qed.

   Lemma dec_context_correct : 
      forall k k' ec v, match dec_context k k' ec v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
       end.

  Proof with auto.
    intros k k' ec.
    dependent destruction ec; simpl...
intro.
dependent destruction v; simpl...
Qed.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match ec, ec0 with 
                | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t  
                | _, _           => False
      end.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
                                     (no associativity, at level 70, ec1, t at level 69).


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_trans :  forall k t ec0 ec1 ec2, 
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 -> 
      k,t |~ ec0 << ec2.

  Proof.
    intros k t ec0 ec1 ec2 H H0.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.



  Lemma search_order_comp_if :                                        forall t k k' k'' (ec0 : elem_context_kinded k k')
     (ec1 : elem_context_kinded k k''),
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
          k, t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ( k' = k'' /\ ec0 ~= ec1).

  Proof.
    intros t k k' k'' ec0 ec1 H0 H1.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.
dependent destruction ec0; dependent destruction ec1;
inversion H5; subst;
    try solve
    [ compute; eautof 7
    | do 2 right; 
      f_equal;
      apply valA_to_term_injective; auto ];
do 2 right;
elim (valA_to_term_injective _ _ H0);
auto.
  Qed.


  Lemma search_order_comp_fi :
    forall t k k' k'' (ec0 : elem_context_kinded k k')
    (ec1 : elem_context_kinded k k''),
       k, t |~ ec0 << ec1 -> 
           immediate_ec ec0 t /\ immediate_ec ec1 t.

  Proof with auto.
    intros t k k' k'' ec0 ec1 H.
dependent destruction ec0; dependent destruction ec1;
inversion H; solve [auto].
  Qed.


  Lemma dec_term_term_top : forall t k {k' t'} (ec : elem_context_kinded k k'), 
            dec_term t k = in_term t' ec -> forall ec', ~ k, t |~ ec << ec'.

  Proof.
    intros t k k' t' ec H ec' H0.
destruct k, t, ec';
revert H0;
inversion H; subst; intro H0; inversion H0...
  Qed.


  Lemma dec_context_red_bot : 
      forall k k' ec v r, dec_context k k' ec v = in_red r -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k k' ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;

    try solve
    [ autof
    | inversion H;
      intro G;
      unfold search_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0; 
      autof ].

  Qed.


  Lemma dec_context_val_bot : 
      forall k k' ec v v', dec_context k k' ec v = in_val v' -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k k' ec v v' H ec'.
    destruct k, ec, ec'; dependent destruction v; 
    solve [ autof ].
  Qed.

  Lemma dec_context_term_next : 
      forall k k' ec0 v t k'' ec1, dec_context k k' ec0 v = @in_term k k'' t ec1 ->
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.

  Proof.
    intros k k' ec0 v t k'' ec1 H.
    dependent destruction ec0;
    dependent destruction ec1;
    try dependent destruction v;
    try solve 
    [ autof

    | inversion H; subst;
      split;
      [ constructor; 
        compute; eauto
      | intros ec'' H0 H1; 
        destruct ec'';
        solve [ autof ] 
      ] ].
  Qed.


  Lemma elem_context_det : 
     forall t k k' (ec : elem_context_kinded k k') {t'}, t = ec:[t'] ->
          forall ec',  k, t |~ ec' << ec ->
              exists (v : value k'), t' = v.

  Proof.
    intros t k k' ec0 t' H ec' H0.
    subst.
    dependent destruction ec0;
    dependent destruction ec';
    autof;
    unfold search_order in H0; destruct H0 as (H, _);
    destruct (valA_is_valF v) as (v0, H0).
    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End Lam_NO_CC_Strategy.



Module Lam_NO_CC_RefSem := RedRefSem Lam_NO_CC_PreRefSem Lam_NO_CC_Strategy.



Require Import refocusing_machine.

Module Lam_NO_CC_EAM := RefEvalApplyMachine Lam_NO_CC_RefSem.

Print Lam_NO_CC_EAM.
